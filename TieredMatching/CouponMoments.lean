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

public import TieredMatching.FirstFresh
public import TieredMatching.CouponTail
public import TieredMatching.CouponBarriers

/-! # Actual IID coupon completion times and elapsed discovery traces

The completion time is the least number of actual stream coordinates covering every coupon,
with value zero on noncompleting streams. Elapsed discovery traces retain the waiting times
that the discovery-order law alone discards.
-/

@[expose] public section

namespace TieredMatching.CouponMoments

open MeasureTheory Set
open scoped NNReal ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Every coupon has appeared strictly before the specified draw count. -/
def covers (x : ℕ → α) (t : ℕ) : Prop := ∀ c, ∃ j < t, x j = c

/-- A stream completes when some finite prefix covers every coupon. -/
def completes (x : ℕ → α) : Prop := ∃ t, covers x t

open scoped Classical in
/-- The actual least cover time, set to zero only on streams that never complete. -/
noncomputable def time (x : ℕ → α) : ℕ := if h : completes x then Nat.find h else 0

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Covering is preserved when the observed prefix grows. -/
theorem covers_mono {x : ℕ → α} {s t : ℕ} (hs : covers x s) (hst : s ≤ t) :
    covers x t := by
  intro c
  obtain ⟨j, hj, he⟩ := hs c
  exact ⟨j, lt_of_lt_of_le hj hst, he⟩

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- On a completing stream, the declared time really covers every coupon. -/
theorem covers_time {x : ℕ → α} (hx : completes x) : covers x (time x) := by
  classical
  simpa only [time, dite_eq_left hx] using Nat.find_spec hx

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The declared time is minimal on every completing stream. -/
theorem time_le_iff {x : ℕ → α} (hx : completes x) (t : ℕ) :
    time x ≤ t ↔ covers x t := by
  classical
  rw [time, dite_eq_left hx]
  exact ⟨fun ht ↦ covers_mono (Nat.find_spec hx) ht, fun ht ↦ Nat.find_min' hx ht⟩

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Finitely many labels each appearing somewhere give a finite cover time. -/
theorem completes_iff (x : ℕ → α) : completes x ↔ ∀ c, ∃ j, x j = c := by
  classical
  constructor
  · rintro ⟨t, ht⟩ c
    obtain ⟨j, _, hj⟩ := ht c
    exact ⟨j, hj⟩
  · intro h
    choose j hj using h
    refine ⟨1 + Finset.univ.sup j, fun c ↦ ⟨j c, ?_, hj c⟩⟩
    have hc := Finset.le_sup (f := j) (Finset.mem_univ c)
    omega

/-- Finite-prefix cover events are measurable cylinders. -/
theorem measurableSet_covers (t : ℕ) : MeasurableSet {x : ℕ → α | covers x t} := by
  have heq : {x : ℕ → α | covers x t} =
      ⋂ c, ⋃ j : Fin t, {x : ℕ → α | x j = c} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, covers]
    constructor
    · intro h c
      obtain ⟨j, hj, he⟩ := h c
      exact ⟨⟨j, hj⟩, he⟩
    · intro h c
      obtain ⟨j, hj⟩ := h c
      exact ⟨j, j.isLt, hj⟩
  rw [heq]
  exact MeasurableSet.iInter fun c ↦ MeasurableSet.iUnion fun j ↦
    measurableSet_eq_fun (measurable_pi_apply (j : ℕ)) measurable_const

/-- The event of eventual completion is measurable. -/
theorem measurableSet_completes : MeasurableSet {x : ℕ → α | completes x} := by
  have heq : {x : ℕ → α | completes x} = ⋃ t, {x | covers x t} := by
    ext x
    simp [completes]
  rw [heq]
  exact MeasurableSet.iUnion measurableSet_covers

/-- The actual least cover time is a measurable natural-valued random variable. -/
theorem measurable_time : Measurable (time : (ℕ → α) → ℕ) := by
  classical
  apply measurable_to_countable
  intro y
  have heq : (time : (ℕ → α) → ℕ) ⁻¹' {time y} =
      ({x | completes x} ∩ {x | covers x (time y)} ∩
        ⋂ j : Fin (time y), {x | covers x j}ᶜ) ∪
      (if time y = 0 then {x | completes x}ᶜ else ∅) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff,
      mem_iInter, mem_compl_iff, mem_ofPred_eq]
    by_cases hx : completes x
    · have hz : x ∉ (if time y = 0 then {x | completes x}ᶜ else ∅) := by
        split_ifs <;> simp [hx]
      simp only [hx, true_and, hz, or_false]
      rw [time, dite_eq_left hx]
      change (Nat.find hx = time y) ↔ _
      have hh := Nat.find_eq_iff (m := time y) (show ∃ t, covers x t from hx)
      simpa only [Fin.forall_iff] using hh
    · simp [time, hx, eq_comm]
  rw [heq]
  apply MeasurableSet.union
  · exact ((measurableSet_completes.inter (measurableSet_covers _)).inter
      (MeasurableSet.iInter fun j ↦ (measurableSet_covers j).compl))
  · split_ifs
    · exact measurableSet_completes.compl
    · exact MeasurableSet.empty

/-- Positive coupon masses ensure actual finite completion almost surely. -/
theorem ae_completes (p : PMF α) (hp : ∀ c, 0 < p c) :
    ∀ᵐ x ∂FirstFresh.iidStream p, completes x := by
  have hc (c : α) : ∀ᵐ x ∂FirstFresh.iidStream p, ∃ j, x j = c := by
    have hs : p.toMeasure ({c}ᶜ) < 1 := by
      rw [measure_compl (measurableSet_singleton c) (measure_ne_top _ _), measure_univ,
        PMF.toMeasure_apply_singleton p c (measurableSet_singleton c)]
      exact ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num) (hp c).ne'
    filter_upwards [FirstFresh.ae_firstFresh p ({c}ᶜ) hs] with x hx
    obtain ⟨j, _, hj⟩ := hx
    exact ⟨j, by simpa using hj⟩
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact (completes_iff x).mpr hx

/-- One designated coupon is absent from the actual first `H` stream coordinates. -/
def missingBefore (H : ℕ) (c : α) : Set (ℕ → α) := {x | ∀ t < H, x t ≠ c}

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Missing-prefix events are finite-coordinate product boxes. -/
theorem missingBefore_eq_pi (H : ℕ) (c : α) :
    missingBefore H c = (Finset.range H : Set ℕ).pi (fun _ ↦ ({c} : Set α)ᶜ) := by
  ext x
  simp [missingBefore, Set.mem_pi]

omit [Fintype α] in
/-- Missing-prefix events are measurable. -/
theorem measurableSet_missingBefore (H : ℕ) (c : α) :
    MeasurableSet (missingBefore H c) := by
  rw [missingBefore_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ ↦
    (measurableSet_singleton c).compl)

/-- Exact no-hit probability for the actual infinite stream's first `H` draws. -/
theorem missingBefore_measure (p : PMF α) (H : ℕ) (c : α) :
    FirstFresh.iidStream p (missingBefore H c) = (p.toMeasure ({c}ᶜ)) ^ H := by
  rw [missingBefore_eq_pi, FirstFresh.iidStream,
    Measure.infinitePi_pi (fun _ : ℕ ↦ p.toMeasure)
      (fun _ _ ↦ (measurableSet_singleton c).compl)]
  simp

/-- Exact real no-hit probability on the actual IID stream. -/
theorem missingBefore_real (p : PMF α) (H : ℕ) (c : α) :
    (FirstFresh.iidStream p).real (missingBefore H c) = (1 - (p c).toReal) ^ H := by
  rw [measureReal_def, missingBefore_measure, ENNReal.toReal_pow]
  change (p.toMeasure.real ({c}ᶜ)) ^ H = _
  rw [probReal_compl_eq_one_sub (measurableSet_singleton c), Coupon.singleton_real]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Failure to cover a finite prefix is exactly a union of missing-coupon events. -/
theorem not_covers_eq_union (H : ℕ) :
    {x : ℕ → α | ¬covers x H} = ⋃ c, missingBefore H c := by
  ext x
  simp [covers, missingBefore, not_forall, not_exists]

/-- The actual coupon completion time has the exact finite-prefix union tail bound. -/
theorem time_tail_le_sum (p : PMF α) (H : ℕ) :
    (FirstFresh.iidStream p).real {x : ℕ → α | H < time x} ≤
      ∑ c, (1 - (p c).toReal) ^ H := by
  have hsub : {x : ℕ → α | H < time x} ⊆ {x : ℕ → α | ¬covers x H} := by
    intro x hx hc
    have hcomplete : completes x := ⟨H, hc⟩
    exact (not_le_of_gt hx) ((time_le_iff hcomplete H).mpr hc)
  calc
    _ ≤ (FirstFresh.iidStream p).real {x : ℕ → α | ¬covers x H} := measureReal_mono hsub
    _ = (FirstFresh.iidStream p).real (⋃ c, missingBefore H c) := by
      rw [not_covers_eq_union]
    _ ≤ ∑ c, (FirstFresh.iidStream p).real (missingBefore H c) :=
      measureReal_iUnion_fintype_le _
    _ = _ := Finset.sum_congr rfl fun c _ ↦ missingBefore_real p H c

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A shifted quadratic times a strictly decaying geometric sequence is summable. -/
theorem summable_shift_sq_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun t : ℕ ↦ ((t : ℝ) + 1) ^ 2 * r ^ t) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have h := (h2.add (h1.mul_left 2)).add h0
  apply h.congr
  intro t
  simp only [pow_one]
  ring

/-- The actual completion-time square is integrable under positive coupon masses.
The proof uses the actual prefix tail, with no assumed stopping-time recurrence. -/
theorem integrable_time_sq (p : PMF α) (hp : ∀ c, 0 < p c) :
    Integrable (fun x : ℕ → α ↦ (time x : ℝ) ^ 2) (FirstFresh.iidStream p) := by
  classical
  have hreal : Measurable (fun x : ℕ → α ↦ (time x : ℝ)) :=
    Measurable.of_discrete.comp measurable_time
  let μ := (FirstFresh.iidStream p).map (time : (ℕ → α) → ℕ)
  have hμ (t : ℕ) : μ.real {t} =
      (FirstFresh.iidStream p).real {x : ℕ → α | time x = t} := by
    rw [measureReal_def, show μ = (FirstFresh.iidStream p).map time from rfl,
      Measure.map_apply measurable_time (measurableSet_singleton t)]
    rfl
  have htail (t : ℕ) : μ.real {t + 1} ≤ ∑ c, (1 - (p c).toReal) ^ t := by
    rw [hμ]
    apply le_trans (measureReal_mono (show {x : ℕ → α | time x = t + 1} ⊆
        {x : ℕ → α | t < time x} from fun x hx ↦ by
          change time x = t + 1 at hx
          change t < time x
          omega))
    exact time_tail_le_sum p t
  have hsum : Summable (fun t : ℕ ↦ ((t : ℝ) + 1) ^ 2 *
      ∑ c, (1 - (p c).toReal) ^ t) := by
    have hc (c : α) : Summable (fun t : ℕ ↦ ((t : ℝ) + 1) ^ 2 *
        (1 - (p c).toReal) ^ t) := by
      apply summable_shift_sq_geometric
      · have hle : (p c).toReal ≤ 1 := by
          rw [← Coupon.singleton_real p c]
          exact measureReal_le_one
        linarith
      · have hpos := ENNReal.toReal_pos (hp c).ne' (p.apply_ne_top c)
        linarith
    have hs := (summable_sum (s := Finset.univ) (fun c _ ↦ hc c))
    simpa only [Finset.mul_sum] using hs
  have hfinite : (∫⁻ x : ℕ → α, ENNReal.ofReal ((time x : ℝ) ^ 2)
      ∂FirstFresh.iidStream p) ≠ ⊤ := by
    have hmap : (∫⁻ x : ℕ → α, ENNReal.ofReal ((time x : ℝ) ^ 2)
        ∂FirstFresh.iidStream p) = ∫⁻ t : ℕ, ENNReal.ofReal ((t : ℝ) ^ 2) ∂μ :=
      (lintegral_map (μ := FirstFresh.iidStream p)
        (f := fun t : ℕ ↦ ENNReal.ofReal ((t : ℝ) ^ 2))
        Measurable.of_discrete measurable_time).symm
    rw [hmap, lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
    simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero,
      zero_mul, zero_add]
    apply ne_of_lt
    calc
      _ ≤ ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) + 1) ^ 2 *
          ∑ c, (1 - (p c).toReal) ^ t) := by
        apply ENNReal.tsum_le_tsum
        intro t
        rw [Nat.cast_add, Nat.cast_one]
        have hmass : μ {t + 1} = ENNReal.ofReal (μ.real {t + 1}) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
        rw [hmass, ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (htail t) (sq_nonneg _))
      _ = ENNReal.ofReal (∑' t : ℕ, ((t : ℝ) + 1) ^ 2 *
          ∑ c, (1 - (p c).toReal) ^ t) := by
        symm
        apply ENNReal.ofReal_tsum_of_nonneg _ hsum
        intro t
        exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun c _ ↦
          pow_nonneg (by
            have hle : (p c).toReal ≤ 1 := by
              rw [← Coupon.singleton_real p c]
              exact measureReal_le_one
            linarith) _)
      _ < ⊤ := ENNReal.ofReal_lt_top
  apply (lintegral_ofReal_ne_top_iff_integrable _ _).mp hfinite
  · exact (hreal.pow measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ ↦ sq_nonneg _

/-- In particular the actual cover time has a finite second moment. -/
theorem memLp_time_two (p : PMF α) (hp : ∀ c, 0 < p c) :
    MemLp (fun x : ℕ → α ↦ (time x : ℝ)) 2 (FirstFresh.iidStream p) := by
  have hreal : Measurable (fun x : ℕ → α ↦ (time x : ℝ)) :=
    Measurable.of_discrete.comp measurable_time
  apply (memLp_two_iff_integrable_sq hreal.aestronglyMeasurable).mpr
  exact integrable_time_sq p hp

/-- The actual cover time is integrable. -/
theorem integrable_time (p : PMF α) (hp : ∀ c, 0 < p c) :
    Integrable (fun x : ℕ → α ↦ (time x : ℝ)) (FirstFresh.iidStream p) :=
  (memLp_time_two p hp).integrable (by norm_num)

/-- A prefix covers all labels outside a specified initially seen set. -/
def seedCovers (S : Set α) (x : ℕ → α) (t : ℕ) : Prop :=
  ∀ c, c ∈ S ∨ ∃ j < t, x j = c

/-- A total predicate for the least remaining cover time; noncompleting streams get zero. -/
def seedPredicate (S : Set α) (x : ℕ → α) (t : ℕ) : Prop :=
  seedCovers S x t ∨ ¬completes x

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The total least-time predicate always has a witness. -/
theorem seed_exists (S : Set α) (x : ℕ → α) : ∃ t, seedPredicate S x t := by
  by_cases hx : completes x
  · obtain ⟨t, ht⟩ := hx
    exact ⟨t, Or.inl fun c ↦ Or.inr (ht c)⟩
  · exact ⟨0, Or.inr hx⟩

open scoped Classical in
/-- Actual remaining cover time, allowing an initially seen set. -/
noncomputable def seedTime (S : Set α) (x : ℕ → α) : ℕ := Nat.find (seed_exists S x)

/-- Remaining-cover events are measurable. -/
theorem measurableSet_seedCovers (S : Set α) (t : ℕ) :
    MeasurableSet {x : ℕ → α | seedCovers S x t} := by
  classical
  have heq : {x : ℕ → α | seedCovers S x t} =
      ⋂ c, if c ∈ S then univ else ⋃ j : Fin t, {x : ℕ → α | x j = c} := by
    ext x
    simp only [mem_ofPred_eq, seedCovers, mem_iInter]
    constructor
    · intro h c
      by_cases hc : c ∈ S
      · simp [hc]
      · obtain ⟨j, hj, he⟩ := (h c).resolve_left hc
        simp only [ite_eq_right hc, mem_iUnion, mem_ofPred_eq]
        exact ⟨⟨j, hj⟩, he⟩
    · intro h c
      by_cases hc : c ∈ S
      · exact Or.inl hc
      · have hh := h c
        simp only [ite_eq_right hc, mem_iUnion, mem_ofPred_eq] at hh
        obtain ⟨j, hj⟩ := hh
        exact Or.inr ⟨j, j.isLt, hj⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.iUnion fun j ↦
      measurableSet_eq_fun (measurable_pi_apply (j : ℕ)) measurable_const

/-- The actual remaining cover time is measurable. -/
theorem measurable_seedTime (S : Set α) : Measurable (seedTime S) := by
  classical
  apply measurable_find (seed_exists S)
  intro t
  exact (measurableSet_seedCovers S t).union measurableSet_completes.compl

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- On completing streams the remaining cover time is the actual least seeded cover time. -/
theorem seedTime_le_iff (S : Set α) {x : ℕ → α} (hx : completes x) (t : ℕ) :
    seedTime S x ≤ t ↔ seedCovers S x t := by
  classical
  constructor
  · intro h c
    have hspec := (Nat.find_spec (seed_exists S x)).resolve_right (not_not.mpr hx)
    obtain hc | ⟨j, hj, he⟩ := hspec c
    · exact Or.inl hc
    · exact Or.inr ⟨j, lt_of_lt_of_le hj h, he⟩
  · intro h
    exact Nat.find_min' (seed_exists S x) (Or.inl h)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A remaining cover time is pointwise bounded by the original full cover time. -/
theorem seedTime_le_time (S : Set α) (x : ℕ → α) : seedTime S x ≤ time x := by
  classical
  by_cases hx : completes x
  · apply (seedTime_le_iff S hx _).mpr
    exact fun c ↦ Or.inr (covers_time hx c)
  · have hzero : seedTime S x = 0 := Nat.eq_zero_of_le_zero
      (Nat.find_min' (seed_exists S x) (show seedPredicate S x 0 from Or.inr hx))
    simp [hzero]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- No draws cover precisely the labels that were already present. -/
theorem seedCovers_zero_iff (S : Set α) (x : ℕ → α) : seedCovers S x 0 ↔ S = univ := by
  simp [seedCovers, Set.eq_univ_iff_forall]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Removing the first actual draw inserts that draw into the seen set. -/
theorem seedCovers_succ_iff (S : Set α) (x : ℕ → α) (t : ℕ) :
    seedCovers S x (t + 1) ↔ seedCovers (insert (x 0) S) (FirstFresh.tailAfter 0 x) t := by
  constructor
  · intro h c
    obtain hc | ⟨j, hj, he⟩ := h c
    · exact Or.inl (Or.inr hc)
    · cases j with
      | zero => exact Or.inl (Or.inl he.symm)
      | succ j =>
        exact Or.inr ⟨j, by omega, by simpa [FirstFresh.tailAfter, Nat.add_comm] using he⟩
  · intro h c
    obtain (hc | hc) | ⟨j, hj, he⟩ := h c
    · exact Or.inr ⟨0, by omega, hc.symm⟩
    · exact Or.inl hc
    · exact Or.inr ⟨j + 1, by omega, by
        simpa [FirstFresh.tailAfter, Nat.add_comm] using he⟩

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The actual remaining completion time obeys the one-draw recursion on completing tails. -/
theorem seedTime_step (S : Set α) (hS : S ≠ univ) {x : ℕ → α}
    (hx : completes x) (htail : completes (FirstFresh.tailAfter 0 x)) :
    seedTime S x = 1 + seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x) := by
  have hpos : seedTime S x ≠ 0 := by
    intro hz
    have hc := (seedTime_le_iff S hx 0).mp (by omega)
    exact hS ((seedCovers_zero_iff S x).mp hc)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hcur := (seedTime_le_iff S hx (seedTime S x)).mp le_rfl
  have hnext := (seedTime_le_iff (insert (x 0) S) htail
    (seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x))).mp le_rfl
  have hupper := (seedTime_le_iff S hx _).mpr ((seedCovers_succ_iff S x _).mpr hnext)
  rw [ht] at hcur
  have hlower := (seedTime_le_iff (insert (x 0) S) htail t).mpr
    ((seedCovers_succ_iff S x t).mp hcur)
  omega

/-- Every remaining cover time has a finite second moment. -/
theorem memLp_seedTime_two (p : PMF α) (hp : ∀ c, 0 < p c) (S : Set α) :
    MemLp (fun x : ℕ → α ↦ (seedTime S x : ℝ)) 2 (FirstFresh.iidStream p) := by
  have hm : Measurable (fun x : ℕ → α ↦ (seedTime S x : ℝ)) :=
    Measurable.of_discrete.comp (measurable_seedTime S)
  apply (memLp_time_two p hp).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (seedTime S x : ℝ) from
    Nat.cast_nonneg _)]
  exact_mod_cast seedTime_le_time S x

/-- Every remaining cover time is integrable. -/
theorem integrable_seedTime (p : PMF α) (hp : ∀ c, 0 < p c) (S : Set α) :
    Integrable (fun x : ℕ → α ↦ (seedTime S x : ℝ)) (FirstFresh.iidStream p) :=
  (memLp_seedTime_two p hp S).integrable (by norm_num)

/-- Restricting to a specified first draw leaves the full future stream with its original
IID law, multiplied by exactly that draw's mass. -/
theorem map_restrict_head_tail (p : PMF α) (q : α) :
    ((FirstFresh.iidStream p).restrict {x : ℕ → α | x 0 = q}).map
      (FirstFresh.tailAfter 0) = p q • FirstFresh.iidStream p := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (FirstFresh.measurable_tailAfter 0) hE,
    Measure.restrict_apply (hE.preimage (FirstFresh.measurable_tailAfter 0)),
    Measure.smul_apply]
  have heq : (FirstFresh.tailAfter 0) ⁻¹' E ∩ {x : ℕ → α | x 0 = q} =
      FirstFresh.hitAt (∅ : Set α) {q} 0 ∩ (FirstFresh.tailAfter 0) ⁻¹' E := by
    ext x
    simp [FirstFresh.hitAt, and_comm]
  rw [heq, FirstFresh.hitAt_tail_measure p ∅ {q} 0 E hE]
  simp [PMF.toMeasure_apply_singleton p q (measurableSet_singleton q)]

/-- Exact first-draw integration against an arbitrary measurable future reward. -/
theorem integral_head_tail (p : PMF α) (q : α) (f : (ℕ → α) → ℝ)
    (hf : Measurable f) :
    (∫ x in {x : ℕ → α | x 0 = q}, f (FirstFresh.tailAfter 0 x)
      ∂FirstFresh.iidStream p) = (p q).toReal * ∫ x, f x ∂FirstFresh.iidStream p := by
  rw [← integral_map (FirstFresh.measurable_tailAfter 0).aemeasurable
    hf.aestronglyMeasurable, map_restrict_head_tail, integral_smul_measure]
  rfl

/-- Integrating a finite choice of future rewards uses its literal first-draw mixture. -/
theorem integral_dispatch (p : PMF α) (f : α → (ℕ → α) → ℝ)
    (hm : ∀ q, Measurable (f q)) (hi : ∀ q, Integrable (f q) (FirstFresh.iidStream p)) :
    (∫ x, f (x 0) (FirstFresh.tailAfter 0 x) ∂FirstFresh.iidStream p) =
      ∑ q, (p q).toReal * ∫ x, f q x ∂FirstFresh.iidStream p := by
  classical
  have hcomp (q : α) : Integrable (fun x ↦ f q (FirstFresh.tailAfter 0 x))
      (FirstFresh.iidStream p) := by
    have hh : Integrable (f q) ((FirstFresh.iidStream p).map (FirstFresh.tailAfter 0)) := by
      rw [FirstFresh.map_tailAfter]
      exact hi q
    exact hh.comp_measurable (FirstFresh.measurable_tailAfter 0)
  have heq (x : ℕ → α) : f (x 0) (FirstFresh.tailAfter 0 x) =
      ∑ q, ({x : ℕ → α | x 0 = q}.indicator
        (fun x ↦ f q (FirstFresh.tailAfter 0 x))) x := by
    simp [Set.indicator, eq_comm]
  simp_rw [heq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    rw [integral_indicator (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const),
      integral_head_tail p q _ (hm q)]
  · intro q _
    exact (hcomp q).indicator (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)

/-- The first moment of the actual remaining cover time. -/
noncomputable def mean (p : PMF α) (S : Set α) : ℝ :=
  ∫ x, (seedTime S x : ℝ) ∂FirstFresh.iidStream p

/-- The second moment of the actual remaining cover time. -/
noncomputable def secondMoment (p : PMF α) (S : Set α) : ℝ :=
  ∫ x, (seedTime S x : ℝ) ^ 2 ∂FirstFresh.iidStream p

/-- The exact first-moment recursion is derived from the actual stream and its fixed-head
regeneration law. It is not a hypothesis on an abstract numeric recurrence. -/
theorem mean_step (p : PMF α) (hp : ∀ c, 0 < p c) (S : Set α) (hS : S ≠ univ) :
    mean p S = 1 + ∑ q, (p q).toReal * mean p (insert q S) := by
  have htail : ∀ᵐ x ∂FirstFresh.iidStream p, completes (FirstFresh.tailAfter 0 x) := by
    have h := ae_completes p hp
    rw [← FirstFresh.map_tailAfter p 0] at h
    exact (ae_map_iff (FirstFresh.measurable_tailAfter 0).aemeasurable
      measurableSet_completes).mp h
  have heq : (fun x : ℕ → α ↦ (seedTime S x : ℝ)) =ᵐ[FirstFresh.iidStream p]
      (fun x ↦ 1 + (seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x) : ℝ)) := by
    filter_upwards [ae_completes p hp, htail] with x hx ht
    exact_mod_cast seedTime_step S hS hx ht
  have hdispatch := integral_dispatch p (fun q x ↦ (seedTime (insert q S) x : ℝ))
    (fun q ↦ Measurable.of_discrete.comp (measurable_seedTime _))
    (fun q ↦ integrable_seedTime p hp _)
  have hcomp : Integrable
      (fun x : ℕ → α ↦ (seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x) : ℝ))
      (FirstFresh.iidStream p) := by
    have hh := (integrable_seedTime p hp S).sub (integrable_const (1 : ℝ))
    apply hh.congr
    filter_upwards [heq] with x hx
    dsimp at hx ⊢
    linarith
  rw [mean, integral_congr_ae heq, integral_add (integrable_const (1 : ℝ)) hcomp,
    integral_const, probReal_univ, one_smul, hdispatch]
  rfl

/-- Exact actual second-moment recursion, with all integrability obligations proved. -/
theorem secondMoment_step (p : PMF α) (hp : ∀ c, 0 < p c)
    (S : Set α) (hS : S ≠ univ) :
    secondMoment p S = ∑ q, (p q).toReal *
      (1 + 2 * mean p (insert q S) + secondMoment p (insert q S)) := by
  have htail : ∀ᵐ x ∂FirstFresh.iidStream p, completes (FirstFresh.tailAfter 0 x) := by
    have h := ae_completes p hp
    rw [← FirstFresh.map_tailAfter p 0] at h
    exact (ae_map_iff (FirstFresh.measurable_tailAfter 0).aemeasurable
      measurableSet_completes).mp h
  have heq : (fun x : ℕ → α ↦ (seedTime S x : ℝ) ^ 2) =ᵐ[FirstFresh.iidStream p]
      (fun x ↦ (1 + (seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x) : ℝ)) ^ 2) := by
    filter_upwards [ae_completes p hp, htail] with x hx ht
    have he : (seedTime S x : ℝ) =
        1 + (seedTime (insert (x 0) S) (FirstFresh.tailAfter 0 x) : ℝ) := by
      exact_mod_cast seedTime_step S hS hx ht
    rw [he]
  have hm (q : α) : Measurable (fun x : ℕ → α ↦ 1 + (seedTime (insert q S) x : ℝ)) :=
    measurable_const.add (Measurable.of_discrete.comp (measurable_seedTime _))
  have hi (q : α) : Integrable (fun x : ℕ → α ↦
      (1 + (seedTime (insert q S) x : ℝ)) ^ 2) (FirstFresh.iidStream p) := by
    apply (memLp_two_iff_integrable_sq (hm q).aestronglyMeasurable).mp
    exact (memLp_const (1 : ℝ)).add (memLp_seedTime_two p hp _)
  rw [secondMoment, integral_congr_ae heq, integral_dispatch p _
    (fun q ↦ (hm q).pow_const 2) hi]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  have htime := integrable_seedTime p hp (insert q S)
  have hsq : Integrable (fun x : ℕ → α ↦ (seedTime (insert q S) x : ℝ) ^ 2)
      (FirstFresh.iidStream p) := by
    apply (memLp_two_iff_integrable_sq
      (Measurable.of_discrete.comp (measurable_seedTime _)).aestronglyMeasurable).mp
    exact memLp_seedTime_two p hp _
  have he (x : ℕ → α) : (1 + (seedTime (insert q S) x : ℝ)) ^ 2 =
      (1 + 2 * (seedTime (insert q S) x : ℝ)) + (seedTime (insert q S) x : ℝ) ^ 2 := by
    ring
  simp_rw [he]
  rw [integral_add (show Integrable (fun x : ℕ → α ↦
      1 + 2 * (seedTime (insert q S) x : ℝ)) (FirstFresh.iidStream p) from
      (integrable_const 1).add (htime.const_mul 2)) hsq,
    integral_add (integrable_const 1) (htime.const_mul 2), integral_const_mul,
    integral_const, probReal_univ, one_smul]
  rfl

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Once every label is initially seen, no further draws are required. -/
theorem seedTime_univ (x : ℕ → α) : seedTime (univ : Set α) x = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min' (seed_exists univ x)
  exact Or.inl fun _ ↦ Or.inl (mem_univ _)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The complete initial state has zero first moment. -/
theorem mean_univ (p : PMF α) : mean p univ = 0 := by simp [mean, seedTime_univ]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The complete initial state has zero second moment. -/
theorem secondMoment_univ (p : PMF α) : secondMoment p univ = 0 := by
  simp [secondMoment, seedTime_univ]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Real masses of all coupon labels sum to one. -/
theorem sum_real_mass (p : PMF α) : ∑ q, (p q).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun q _ ↦ p.apply_ne_top q)]
  have hh : ∑ q, p q = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [hh]
  rfl

open scoped Classical in
/-- Unseen coupon labels in a specified state. -/
noncomputable def unseen (S : Set α) : Finset α := Finset.univ.filter (fun q ↦ q ∉ S)

/-- The exact fresh-mass-scaled first-moment recursion after cancelling repeat draws. -/
theorem mean_fresh_step (p : PMF α) (hp : ∀ c, 0 < p c) (S : Set α) (hS : S ≠ univ) :
    (∑ q ∈ unseen S, (p q).toReal) * mean p S =
      1 + ∑ q ∈ unseen S, (p q).toReal * mean p (insert q S) := by
  classical
  have hterm (q : α) : (if q ∉ S then (p q).toReal *
      (mean p S - mean p (insert q S)) else 0) =
      (p q).toReal * (mean p S - mean p (insert q S)) := by
    by_cases hq : q ∈ S
    · simp [hq, Set.insert_eq_of_mem hq]
    · simp [hq]
  have hsum : (∑ q ∈ unseen S, (p q).toReal *
      (mean p S - mean p (insert q S))) = 1 := by
    simp only [unseen, Finset.sum_filter, hterm]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_real_mass, one_mul]
    have hm := mean_step p hp S hS
    linarith
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  linarith

/-- The exact fresh-mass-scaled second-moment recursion after cancelling repeat draws. -/
theorem secondMoment_fresh_step (p : PMF α) (hp : ∀ c, 0 < p c)
    (S : Set α) (hS : S ≠ univ) :
    (∑ q ∈ unseen S, (p q).toReal) * secondMoment p S =
      2 * mean p S - 1 + ∑ q ∈ unseen S, (p q).toReal * secondMoment p (insert q S) := by
  classical
  have hterm (q : α) : (if q ∉ S then (p q).toReal *
      (secondMoment p S - secondMoment p (insert q S)) else 0) =
      (p q).toReal * (secondMoment p S - secondMoment p (insert q S)) := by
    by_cases hq : q ∈ S
    · simp [hq, Set.insert_eq_of_mem hq]
    · simp [hq]
  have hs := secondMoment_step p hp S hS
  have hm := mean_step p hp S hS
  have hexpand : (∑ q, (p q).toReal *
      (1 + 2 * mean p (insert q S) + secondMoment p (insert q S))) =
      1 + 2 * (∑ q, (p q).toReal * mean p (insert q S)) +
        ∑ q, (p q).toReal * secondMoment p (insert q S) := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_real_mass]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hexpand] at hs
  have hsum : (∑ q ∈ unseen S, (p q).toReal *
      (secondMoment p S - secondMoment p (insert q S))) = 2 * mean p S - 1 := by
    simp only [unseen, Finset.sum_filter, hterm]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_real_mass, one_mul]
    linarith
  simp_rw [mul_sub] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  linarith

/-- Actual time to collect a specified remaining finite set. -/
noncomputable def remainingMean (p : PMF α) (R : Finset α) : ℝ := mean p (R : Set α)ᶜ

/-- Actual second moment for a specified remaining finite set. -/
noncomputable def remainingSecondMoment (p : PMF α) (R : Finset α) : ℝ :=
  secondMoment p (R : Set α)ᶜ

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Taking the complement of a remaining set recovers exactly those unseen coupons. -/
theorem unseen_compl_coe (R : Finset α) : unseen (R : Set α)ᶜ = R := by
  classical
  ext q
  simp [unseen]

open scoped Classical in
omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Removing one remaining label is the same as inserting it into the seen set. -/
theorem insert_compl_coe (R : Finset α) (q : α) :
    insert q (R : Set α)ᶜ = ((R.erase q : Finset α) : Set α)ᶜ := by
  ext c
  simp [eq_comm]
  tauto

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A nonempty remaining set has a proper initially seen complement. -/
theorem compl_coe_ne_univ {R : Finset α} (hR : R.Nonempty) : (R : Set α)ᶜ ≠ univ := by
  obtain ⟨q, hq⟩ := hR
  intro he
  have hmem : q ∈ (R : Set α)ᶜ := he.symm ▸ mem_univ q
  exact hmem hq

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The empty remaining set takes no time. -/
theorem remainingMean_empty (p : PMF α) : remainingMean p ∅ = 0 := by
  simp [remainingMean, mean_univ]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The empty remaining set has zero second moment. -/
theorem remainingSecondMoment_empty (p : PMF α) : remainingSecondMoment p ∅ = 0 := by
  simp [remainingSecondMoment, secondMoment_univ]

open scoped Classical in
/-- Actual mean recursion in the remaining-set interface used by harmonic barriers. -/
theorem remainingMean_step (p : PMF α) (hp : ∀ c, 0 < p c) (R : Finset α)
    (hR : R.Nonempty) :
    (∑ q ∈ R, (p q).toReal) * remainingMean p R =
      1 + ∑ q ∈ R, (p q).toReal * remainingMean p (R.erase q) := by
  simpa only [remainingMean, unseen_compl_coe, insert_compl_coe] using
    mean_fresh_step p hp (R : Set α)ᶜ (compl_coe_ne_univ hR)

open scoped Classical in
/-- Actual second-moment recursion in the remaining-set harmonic-barrier interface. -/
theorem remainingSecondMoment_step (p : PMF α) (hp : ∀ c, 0 < p c) (R : Finset α)
    (hR : R.Nonempty) :
    (∑ q ∈ R, (p q).toReal) * remainingSecondMoment p R =
      2 * remainingMean p R - 1 +
        ∑ q ∈ R, (p q).toReal * remainingSecondMoment p (R.erase q) := by
  simpa only [remainingMean, remainingSecondMoment, unseen_compl_coe, insert_compl_coe] using
    secondMoment_fresh_step p hp (R : Set α)ᶜ (compl_coe_ne_univ hR)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- With no labels initially seen the remaining time is exactly the original cover time. -/
theorem seedTime_empty (x : ℕ → α) : seedTime (∅ : Set α) x = time x := by
  classical
  by_cases hx : completes x
  · apply Nat.le_antisymm (seedTime_le_time ∅ x)
    apply (time_le_iff hx _).mpr
    have hc := (seedTime_le_iff ∅ hx (seedTime ∅ x)).mp le_rfl
    intro c
    simpa using hc c
  · have hle := seedTime_le_time ∅ x
    simpa [time, hx] using hle

omit [MeasurableSingletonClass α] in
/-- The full remaining-set mean is the actual stream's cover-time expectation. -/
theorem remainingMean_univ (p : PMF α) :
    remainingMean p Finset.univ = ∫ x, (time x : ℝ) ∂FirstFresh.iidStream p := by
  simp [remainingMean, mean, seedTime_empty]

omit [MeasurableSingletonClass α] in
/-- The full remaining-set second moment is the actual cover-time second moment. -/
theorem remainingSecondMoment_univ (p : PMF α) :
    remainingSecondMoment p Finset.univ =
      ∫ x, (time x : ℝ) ^ 2 ∂FirstFresh.iidStream p := by
  simp [remainingSecondMoment, secondMoment, seedTime_empty]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Every actual remaining-set mean is nonnegative. -/
theorem remainingMean_nonneg (p : PMF α) (R : Finset α) : 0 ≤ remainingMean p R := by
  apply integral_nonneg
  intro x
  exact Nat.cast_nonneg _

/-- Collecting a subset cannot take longer in expectation than collecting every label. -/
theorem remainingMean_le_full (p : PMF α) (hp : ∀ c, 0 < p c) (R : Finset α) :
    remainingMean p R ≤ ∫ x, (time x : ℝ) ∂FirstFresh.iidStream p := by
  apply integral_mono (integrable_seedTime p hp _) (integrable_time p hp)
  intro x
  change (seedTime (R : Set α)ᶜ x : ℝ) ≤ (time x : ℝ)
  exact_mod_cast seedTime_le_time (R : Set α)ᶜ x

/-- Variance of the actual cover time is its actual second moment minus squared mean. -/
theorem variance_time_eq (p : PMF α) (hp : ∀ c, 0 < p c) :
    ProbabilityTheory.variance (fun x : ℕ → α ↦ (time x : ℝ)) (FirstFresh.iidStream p) =
      remainingSecondMoment p Finset.univ - (remainingMean p Finset.univ) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_time_two p hp),
    remainingMean_univ, remainingSecondMoment_univ]
  rfl

/-- Total real coupon weight. -/
noncomputable def totalWeight (weight : α → ℝ≥0) : ℝ := ∑ q, (weight q : ℝ)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A nonempty market with positive weights has positive total weight. -/
theorem totalWeight_pos [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 0 < weight q) :
    0 < totalWeight weight := by
  exact Finset.sum_pos (fun q _ ↦ hw q) Finset.univ_nonempty

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Normalizing positive weights gives positive masses for all actual coupon draws. -/
theorem ofWeights_mass_pos [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 0 < weight q)
    (q : α) : 0 < RandomRanking.ofWeights weight q := by
  have htotal : (∑ q, weight q) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun q _ ↦ hw q) Finset.univ_nonempty)
  rw [RandomRanking.ofWeights_apply weight htotal]
  exact ENNReal.div_pos (by exact_mod_cast (hw q).ne') (by simp)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Real normalized categorical mass times total weight is exactly its original weight. -/
theorem ofWeights_weighted_mass [Nonempty α] (weight : α → ℝ≥0)
    (hw : ∀ q, 0 < weight q) (q : α) :
    totalWeight weight * (RandomRanking.ofWeights weight q).toReal = (weight q : ℝ) := by
  have htotal : (∑ q, weight q) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun q _ ↦ hw q) Finset.univ_nonempty)
  rw [RandomRanking.ofWeights_apply weight htotal, ENNReal.toReal_div]
  simp only [ENNReal.coe_toReal, NNReal.coe_sum]
  change totalWeight weight * ((weight q : ℝ) / totalWeight weight) = _
  exact mul_div_cancel₀ _ (totalWeight_pos weight hw).ne'

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- For weights at least one, every coupon mass is at least the reciprocal total weight. -/
theorem ofWeights_mass_lower [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q)
    (q : α) : 1 ≤ totalWeight weight * (RandomRanking.ofWeights weight q).toReal := by
  rw [ofWeights_weighted_mass weight (fun q ↦ lt_of_lt_of_le (by norm_num) (hw q)) q]
  exact_mod_cast hw q

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- An individual minimum-weight coupon has mass exactly the reciprocal total weight. -/
theorem ofWeights_mass_one [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 0 < weight q)
    (q : α) (hq : weight q = 1) :
    totalWeight weight * (RandomRanking.ofWeights weight q).toReal = 1 := by
  rw [ofWeights_weighted_mass weight hw q, hq]
  rfl

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The score floor one bounds the number of coupons by total weight. -/
theorem card_le_totalWeight (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q) :
    (Fintype.card α : ℝ) ≤ totalWeight weight := by
  calc
    _ = ∑ _q : α, (1 : ℝ) := by simp
    _ ≤ ∑ q, (weight q : ℝ) := Finset.sum_le_sum fun q _ ↦ by exact_mod_cast hw q

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The score ceiling gives the uniform linear total-weight upper bound. -/
theorem totalWeight_le_card_mul (weight : α → ℝ≥0) (A : ℝ) (hw : ∀ q, (weight q : ℝ) ≤ A) :
    totalWeight weight ≤ (Fintype.card α : ℝ) * A := by
  calc
    _ ≤ ∑ _q : α, A := Finset.sum_le_sum fun q _ ↦ hw q
    _ = _ := by simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Reciprocal-total-weight lower mass in the exact normalized categorical law. -/
theorem ofWeights_real_ge_inv [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q)
    (q : α) : 1 / totalWeight weight ≤ (RandomRanking.ofWeights weight q).toReal := by
  have hpos := totalWeight_pos weight (fun q ↦ lt_of_lt_of_le (by norm_num) (hw q))
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using ofWeights_mass_lower weight hw q

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The exact reciprocal mass of a minimum-score coupon. -/
theorem ofWeights_real_eq_inv [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 0 < weight q)
    (q : α) (hq : weight q = 1) :
    (RandomRanking.ofWeights weight q).toReal = 1 / totalWeight weight := by
  apply (eq_div_iff (totalWeight_pos weight hw).ne').mpr
  simpa only [mul_comm] using ofWeights_mass_one weight hw q hq

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Real harmonic numbers increase with their natural index. -/
theorem harmonic_cast_mono : Monotone (fun r : ℕ ↦ (harmonic r : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro r
  simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))

open scoped Classical in
/-- The finite set of minimum-score coupons in a normalized market. -/
noncomputable def minimumCoupons (weight : α → ℝ≥0) : Finset α :=
  Finset.univ.filter fun q ↦ weight q = 1

/-- The actual IID cover-time expectation has the exact leading harmonic upper bound. -/
theorem mean_time_le_harmonic [Nonempty α] (weight : α → ℝ≥0)
    (hw : ∀ q, 1 ≤ weight q) :
    (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      totalWeight weight * (harmonic (Fintype.card α) : ℝ) := by
  classical
  have hpos : ∀ q, 0 < weight q := fun q ↦ lt_of_lt_of_le (by norm_num) (hw q)
  have hp := ofWeights_mass_pos weight hpos
  have hh := CouponBarriers.mean_le_barrier
    (fun q ↦ (RandomRanking.ofWeights weight q).toReal)
    (remainingMean (RandomRanking.ofWeights weight)) (totalWeight_pos weight hpos)
    (ofWeights_real_ge_inv weight hw) (remainingMean_empty _)
    (remainingMean_step _ hp) Finset.univ
  simpa only [remainingMean_univ, Finset.card_univ, CouponBarriers.meanBarrier] using hh

/-- A target subset of minimum-score coupons has exact harmonic expected collection time. -/
theorem remainingMean_minimumCoupons [Nonempty α] (weight : α → ℝ≥0)
    (hw : ∀ q, 0 < weight q) :
    remainingMean (RandomRanking.ofWeights weight) (minimumCoupons weight) =
      totalWeight weight * (harmonic (minimumCoupons weight).card : ℝ) := by
  classical
  apply CouponBarriers.mean_eq_barrier_of_equal_mass_on
    (fun q ↦ (RandomRanking.ofWeights weight q).toReal)
    (remainingMean (RandomRanking.ofWeights weight)) (totalWeight_pos weight hw)
    (remainingMean_empty _) (remainingMean_step _ (ofWeights_mass_pos weight hw))
  intro q hq
  exact ofWeights_real_eq_inv weight hw q (by simpa [minimumCoupons] using hq)

/-- At least `k` score-one coupons force the actual harmonic lower bound. -/
theorem harmonic_le_mean_time [Nonempty α] (weight : α → ℝ≥0)
    (hw : ∀ q, 0 < weight q) (k : ℕ) (hk : k ≤ (minimumCoupons weight).card) :
    totalWeight weight * (harmonic k : ℝ) ≤
      ∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight) := by
  calc
    _ ≤ totalWeight weight * (harmonic (minimumCoupons weight).card : ℝ) :=
      mul_le_mul_of_nonneg_left (harmonic_cast_mono hk) (totalWeight_pos weight hw).le
    _ = remainingMean (RandomRanking.ofWeights weight) (minimumCoupons weight) :=
      (remainingMean_minimumCoupons weight hw).symm
    _ ≤ _ := remainingMean_le_full _ (ofWeights_mass_pos weight hw) _

/-- A logarithmic upper bound with the source's exact leading total-weight coefficient. -/
theorem mean_time_le_log [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q) :
    (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      totalWeight weight * (1 + Real.log (Fintype.card α)) := by
  apply (mean_time_le_harmonic weight hw).trans
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (totalWeight_pos weight
    (fun q ↦ lt_of_lt_of_le (by norm_num) (hw q))).le

/-- Minimum-score coupons give the logarithmic lower bound with exact leading coefficient. -/
theorem log_le_mean_time [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 0 < weight q)
    (k : ℕ) (hk : k ≤ (minimumCoupons weight).card) :
    totalWeight weight * Real.log (k + 1 : ℕ) ≤
      ∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight) := by
  apply le_trans _ (harmonic_le_mean_time weight hw k hk)
  exact mul_le_mul_of_nonneg_left (log_add_one_le_harmonic k) (totalWeight_pos weight hw).le

/-- The actual IID cover time has the source's second-moment bound with coefficient two. -/
theorem secondMoment_time_le [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q) :
    (∫ x, (time x : ℝ) ^ 2 ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      (totalWeight weight * (harmonic (Fintype.card α) : ℝ)) ^ 2 +
        2 * totalWeight weight ^ 2 := by
  classical
  have hpos : ∀ q, 0 < weight q := fun q ↦ lt_of_lt_of_le (by norm_num) (hw q)
  have hp := ofWeights_mass_pos weight hpos
  have hh := CouponBarriers.secondMoment_le_meanBarrier_sq_add_two_mul_sq
    (fun q ↦ (RandomRanking.ofWeights weight q).toReal)
    (remainingMean (RandomRanking.ofWeights weight))
    (remainingSecondMoment (RandomRanking.ofWeights weight)) (totalWeight_pos weight hpos)
    (ofWeights_real_ge_inv weight hw) (remainingMean_empty _) (remainingMean_step _ hp)
    (remainingSecondMoment_empty _) (remainingSecondMoment_step _ hp) Finset.univ
    (by simpa using card_le_totalWeight weight hw)
  simpa only [remainingSecondMoment_univ, Finset.card_univ, CouponBarriers.meanBarrier] using hh

/-- The actual cover-time variance bound used by the source coupon comparison. -/
theorem variance_time_le [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q) :
    ProbabilityTheory.variance (fun x : ℕ → α ↦ (time x : ℝ))
      (FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      2 * totalWeight weight ^ 2 +
        (totalWeight weight * (harmonic (Fintype.card α) : ℝ)) ^ 2 -
        (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ^ 2 := by
  have hpos : ∀ q, 0 < weight q := fun q ↦ lt_of_lt_of_le (by norm_num) (hw q)
  rw [variance_time_eq _ (ofWeights_mass_pos weight hpos), remainingMean_univ,
    remainingSecondMoment_univ]
  have hh := secondMoment_time_le weight hw
  linarith

/-- Exact actual IID coupon moment bounds, including almost-sure completion and a finite
second moment. The minimum-score count may be any `k` below the number of score-one labels. -/
theorem coupon_time_moments [Nonempty α] (weight : α → ℝ≥0) (hw : ∀ q, 1 ≤ weight q)
    (k : ℕ) (hk : k ≤ (minimumCoupons weight).card) :
    (∀ᵐ x ∂FirstFresh.iidStream (RandomRanking.ofWeights weight), completes x) ∧
    MemLp (fun x : ℕ → α ↦ (time x : ℝ)) 2
      (FirstFresh.iidStream (RandomRanking.ofWeights weight)) ∧
    totalWeight weight * (harmonic k : ℝ) ≤
      (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ∧
    (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      totalWeight weight * (harmonic (Fintype.card α) : ℝ) ∧
    ProbabilityTheory.variance (fun x : ℕ → α ↦ (time x : ℝ))
      (FirstFresh.iidStream (RandomRanking.ofWeights weight)) ≤
      2 * totalWeight weight ^ 2 +
        (totalWeight weight * (harmonic (Fintype.card α) : ℝ)) ^ 2 -
        (∫ x, (time x : ℝ) ∂FirstFresh.iidStream (RandomRanking.ofWeights weight)) ^ 2 := by
  have hpos : ∀ q, 0 < weight q := fun q ↦ lt_of_lt_of_le (by norm_num) (hw q)
  have hp := ofWeights_mass_pos weight hpos
  exact ⟨ae_completes _ hp, memLp_time_two _ hp, harmonic_le_mean_time weight hpos k hk,
    mean_time_le_harmonic weight hw, variance_time_le weight hw⟩

open scoped Classical in
/-- A discovery trace specifies each newly discovered label and its preceding repeat count. -/
noncomputable def traceEvent (S : Set α) : List (α × ℕ) → Set (ℕ → α)
  | [] => univ
  | (q, k) :: L => if q ∈ S then ∅ else
      FirstFresh.hitAt S {q} k ∩
        (FirstFresh.tailAfter k) ⁻¹' traceEvent (insert q S) L

/-- Discovery traces with specified elapsed waiting times are measurable. -/
theorem measurableSet_traceEvent (S : Set α) (L : List (α × ℕ)) :
    MeasurableSet (traceEvent S L) := by
  classical
  induction L generalizing S with
  | nil => exact MeasurableSet.univ
  | cons a L ih =>
    obtain ⟨q, k⟩ := a
    rw [traceEvent]
    split_ifs
    · exact MeasurableSet.empty
    · exact (FirstFresh.measurableSet_hitAt S {q} k).inter
        ((ih _).preimage (FirstFresh.measurable_tailAfter k))

open scoped Classical in
/-- The explicit elapsed-trace likelihood, before any waiting times are summed out. -/
noncomputable def traceMass (p : PMF α) (S : Set α) : List (α × ℕ) → ℝ≥0∞
  | [] => 1
  | (q, k) :: L => if q ∈ S then 0 else
      (p.toMeasure S) ^ k * p q * traceMass p (insert q S) L

/-- The actual stream has the exact product likelihood for every elapsed discovery trace.
This uses fixed-time head/tail independence, rather than assuming conditional waiting laws. -/
theorem traceEvent_measure (p : PMF α) (S : Set α) (L : List (α × ℕ)) :
    FirstFresh.iidStream p (traceEvent S L) = traceMass p S L := by
  classical
  induction L generalizing S with
  | nil => simp [traceEvent, traceMass]
  | cons a L ih =>
    obtain ⟨q, k⟩ := a
    by_cases hq : q ∈ S
    · simp [traceEvent, traceMass, hq]
    · rw [traceEvent, ite_eq_right hq, FirstFresh.hitAt_tail_measure p S {q} k _
        (measurableSet_traceEvent _ _), ih, traceMass, ite_eq_right hq,
        PMF.toMeasure_apply_singleton p q (measurableSet_singleton q)]

end TieredMatching.CouponMoments
