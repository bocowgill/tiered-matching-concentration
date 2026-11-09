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

public import TieredMatching.StoppedProcess
public import TieredMatching.CompetingHazards

/-!
# Actual finite observation processes with competing destinations

Each visible branch is observed from the same original path law. Literal prefix refinement
proves disintegration, and a backward potential bounds its actual protected-target avoidance
probability. Strict chronological progress makes sufficiently long truncations agree.
-/

@[expose] public section

namespace TieredMatching.CompetingProcess

open FiniteConditioning CompetingHazards StoppedHazards
open scoped ENNReal

/-- A finite visible-boundary process; no outcome tree or transition law is supplied.
The destination constructor makes target/empty/neutral flags visible and mutually exclusive. -/
structure Process (Ω : Type*) (M : ℕ) (A : ℝ) where
  law : PMF Ω
  event : Fin M → Set Ω
  remaining : Fin M → ℕ
  stopped : Fin M → Bool
  next : Fin M → Ω → Fin M
  kind : Fin M → Fin M → Destination
  clock : Fin M → ℕ
  cap : ℕ
  refines : ∀ h j, eventMass law (event h) ≠ 0 →
    ((condition law (event h)).map (next h)) j ≠ 0 →
    event j = event h ∩ {ω | next h ω = j}
  zero_stopped : ∀ h, remaining h = 0 → stopped h = true
  cap_stopped : ∀ h, cap ≤ clock h → stopped h = true
  progress : ∀ h j, eventMass law (event h) ≠ 0 → stopped h = false →
    ((condition law (event h)).map (next h)) j ≠ 0 → clock h < clock j
  remaining_next : ∀ h j, eventMass law (event h) ≠ 0 → stopped h = false →
    ((condition law (event h)).map (next h)) j ≠ 0 →
    remaining j = if kind h j = .empty then remaining h - 1 else remaining h
  hazard : ∀ h, eventMass law (event h) ≠ 0 → stopped h = false →
    mass ((condition law (event h)).map (next h)) (kind h) .target ≤
      A * mass ((condition law (event h)).map (next h)) (kind h) .empty

namespace Process

variable {Ω : Type*} {M : ℕ} {A : ℝ} (D : Process Ω M A)

/-- The original path law conditioned on its current visible prefix event. -/
noncomputable def conditional (h : Fin M) : PMF Ω := condition D.law (D.event h)

/-- The next boundary law is derived by observing the same conditional full path. -/
noncomputable def transition (h : Fin M) : PMF (Fin M) :=
  (D.conditional h).map (D.next h)

/-- Nonnull boundary branches have nonnull original prefix events. -/
theorem child_nonnull (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) : eventMass D.law (D.event j) ≠ 0 := by
  rw [D.refines h j hh hj, ← eventMass_mul_conditional_event,
    eventMass_observation_fiber]
  exact mul_ne_zero hh hj

/-- The branch's conditional law is literally the original law at the child prefix. -/
theorem condition_next (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) :
    condition (D.conditional h) {ω | D.next h ω = j} = D.conditional j := by
  rw [conditional, conditional, D.refines h j hh hj]
  exact StoppedProcess.condition_inter D.law _ _ (by
    rw [← D.refines h j hh hj]
    exact D.child_nonnull h j hh hj)

/-- Actual boundary tower identity, proved from prefix refinement rather than assumed. -/
theorem boundary_disintegration (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (D.transition h).bind D.conditional = D.conditional h := by
  calc
    _ = (D.transition h).bind
        (fun j ↦ condition (D.conditional h) {ω | D.next h ω = j}) := by
      apply StoppedProcess.bind_congr_support
      intro j hj
      exact (D.condition_next h j hh hj).symm
    _ = D.conditional h := bind_condition_eq _ _

/-- A child-prefix-supported path has that child's visible predecessor observation. -/
theorem child_support_next (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) (ω : Ω) (hω : D.conditional j ω ≠ 0) : D.next h ω = j := by
  have hs : ω ∈ (condition D.law (D.event j)).support := hω
  rw [support_condition D.law (D.event j) (D.child_nonnull h j hh hj)] at hs
  rw [D.refines h j hh hj] at hs
  exact hs.1.2

/-- Every supported full path induces a positive next branch. -/
theorem next_supported (h : Fin M) (ω : Ω) (hω : D.conditional h ω ≠ 0) :
    D.transition h (D.next h ω) ≠ 0 := by
  exact (PMF.mem_support_map_iff (D.next h) (D.conditional h) _).mpr ⟨ω, hω, rfl⟩

/-- The same full path stays supported after its observed boundary is revealed. -/
theorem path_supported_child (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (ω : Ω) (hω : D.conditional h ω ≠ 0) : D.conditional (D.next h ω) ω ≠ 0 := by
  have hp : ω ∈ (condition D.law (D.event h)).support := hω
  rw [support_condition D.law (D.event h) hh] at hp
  have hj := D.next_supported h ω hω
  have hs : ω ∈ (D.conditional (D.next h ω)).support := by
    rw [conditional, support_condition D.law _ (D.child_nonnull h _ hh hj),
      D.refines h _ hh hj]
    exact ⟨⟨hp.1, rfl⟩, hp.2⟩
  exact hs

/-- The actual pathwise avoidance outcome through a finite number of visible boundaries.
Stops and finite caps are safe; a target branch fails before its child is visited. -/
def safeFuel : ℕ → Fin M → Ω → Bool
  | 0, _, _ => true
  | k + 1, h, ω => if D.stopped h then true else
      if D.kind h (D.next h ω) = .target then false else safeFuel k (D.next h ω) ω

/-- The law of the actual finite pathwise avoidance outcome. -/
noncomputable def safeLawFuel (k : ℕ) (h : Fin M) : PMF Bool :=
  (D.conditional h).map (D.safeFuel k h)

/-- Exact outcome-law recurrence derived from the same original path at each child prefix. -/
theorem safe_map_succ (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hs : D.stopped h = false) :
    D.safeLawFuel (k + 1) h = (D.transition h).bind fun j ↦
      if D.kind h j = .target then PMF.pure false else D.safeLawFuel k j := by
  unfold safeLawFuel
  conv_lhs => rw [← D.boundary_disintegration h hh]
  rw [PMF.map_bind]
  apply StoppedProcess.bind_congr_support
  intro j hj
  by_cases ht : D.kind h j = .target
  · rw [ite_eq_left ht]
    have heq : (D.conditional j).map (D.safeFuel (k + 1) h) =
        (D.conditional j).map (Function.const Ω false) := by
      apply StoppedProcess.Process.map_congr_support
      intro ω hω
      simp only [safeFuel, hs, Bool.false_eq_true, ↓reduceIte,
        D.child_support_next h j hh hj ω hω, ht, Function.const_apply]
    rw [heq, PMF.map_const]
  · rw [ite_eq_right ht]
    apply StoppedProcess.Process.map_congr_support
    intro ω hω
    simp only [safeFuel, hs, Bool.false_eq_true, ↓reduceIte,
      D.child_support_next h j hh hj ω hω, ht]

/-- Backward induction bounds the success probability of the actual mapped path outcome.
Only current visible-history competing masses enter the induction. -/
theorem ofReal_potential_le_successFuel (hA : 0 ≤ A) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    ENNReal.ofReal (CompetingHazards.potential A (D.remaining h)) ≤ D.safeLawFuel k h true := by
  induction k generalizing h with
  | zero =>
    change ENNReal.ofReal _ ≤ ((D.conditional h).map (Function.const Ω true)) true
    rw [PMF.map_const]
    simpa only [PMF.pure_apply, ↓reduceIte, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (CompetingHazards.potential_le_one hA (D.remaining h))
  | succ k ih =>
    by_cases hs : D.stopped h = true
    · have hsaf : D.safeFuel (k + 1) h = Function.const Ω true := by
        funext ω
        simp only [safeFuel, hs, ↓reduceIte, Function.const_apply]
      simp only [safeLawFuel, hsaf, PMF.map_const, PMF.pure_apply, ↓reduceIte]
      exact ENNReal.ofReal_le_one.mpr (CompetingHazards.potential_le_one hA (D.remaining h))
    have hs' := Bool.eq_false_iff.mpr hs
    have hrem : D.remaining h ≠ 0 := fun hz ↦ hs (D.zero_stopped h hz)
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hrem
    rw [← CompetingHazards.expectation_success, D.safe_map_succ k h hh hs', expectation_bind, hr]
    calc
      ENNReal.ofReal (CompetingHazards.potential A (r + 1)) ≤
          ENNReal.ofReal (∑ j, (D.transition h j).toReal *
            CompetingHazards.reward A r (D.kind h j)) :=
        ENNReal.ofReal_le_ofReal (CompetingHazards.potential_le_weighted_reward hA
          (D.transition h) (D.kind h) r (D.hazard h hh hs'))
      _ = expectation (D.transition h)
          (fun j ↦ ENNReal.ofReal (CompetingHazards.reward A r (D.kind h j))) := by
        symm
        apply expectation_ofReal
        intro j
        cases D.kind h j <;> simp [CompetingHazards.reward,
          (CompetingHazards.potential_pos hA r).le,
          (CompetingHazards.potential_pos hA (r + 1)).le]
      _ ≤ _ := by
        apply StoppedProcess.Process.expectation_mono_support
        intro j hj
        by_cases ht : D.kind h j = .target
        · simp [ht, CompetingHazards.reward, expectation_pure]
        · rw [ite_eq_right ht, CompetingHazards.expectation_success]
          have hchild := D.remaining_next h j hh hs' hj
          have heq : CompetingHazards.reward A r (D.kind h j) =
              CompetingHazards.potential A (D.remaining j) := by
            rw [hchild, hr]
            cases he : D.kind h j <;> simp_all [CompetingHazards.reward]
          rw [heq]
          exact ih j (D.child_nonnull h j hh hj)

/-- Real success probability of the actual finite-horizon avoidance outcome. -/
theorem potential_le_successFuel (hA : 0 ≤ A) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    CompetingHazards.potential A (D.remaining h) ≤ (D.safeLawFuel k h true).toReal := by
  have hb := ENNReal.toReal_mono ((D.safeLawFuel k h).apply_ne_top true)
    (D.ofReal_potential_le_successFuel hA k h hh)
  simpa only [ENNReal.toReal_ofReal (CompetingHazards.potential_pos hA (D.remaining h)).le]
    using hb

/-- The complementary actual failure probability has the matching upper bound. -/
theorem failureFuel_le_one_sub_potential (hA : 0 ≤ A) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    (D.safeLawFuel k h false).toReal ≤ 1 - CompetingHazards.potential A (D.remaining h) := by
  have hs : D.safeLawFuel k h false + D.safeLawFuel k h true = 1 := by
    simpa [tsum_fintype, add_comm] using (D.safeLawFuel k h).tsum_coe
  have hr : (D.safeLawFuel k h false).toReal + (D.safeLawFuel k h true).toReal = 1 := by
    rw [← ENNReal.toReal_add ((D.safeLawFuel k h).apply_ne_top false)
      ((D.safeLawFuel k h).apply_ne_top true), hs]
    rfl
  have hb := D.potential_le_successFuel hA k h hh
  linarith

/-- The uniform two-empty lower bound applies to the actual path event, including caps. -/
theorem two_empty_le_successFuel (hA : 0 ≤ A) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : D.remaining h ≤ 2) :
    CompetingHazards.potential A 2 ≤ (D.safeLawFuel k h true).toReal := by
  refine le_trans ?_ (D.potential_le_successFuel hA k h hh)
  exact pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith))
    ((inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)) hk

/-- The same bound on the actual conditional event of seeing a protected-target branch. -/
theorem failure_eventFuel_le (hA : 0 ≤ A) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    (eventMass (D.conditional h) {ω | D.safeFuel k h ω = false}).toReal ≤
      1 - CompetingHazards.potential A (D.remaining h) := by
  rw [eventMass_observation_fiber]
  exact D.failureFuel_le_one_sub_potential hA k h hh

/-- A visibly stopped history is safe at every horizon. -/
theorem safeFuel_of_stopped (k : ℕ) (h : Fin M) (ω : Ω)
    (hs : D.stopped h = true) : D.safeFuel k h ω = true := by
  cases k <;> simp [safeFuel, hs]

/-- Chronological progress eliminates the arbitrary truncation once its horizon reaches cap. -/
theorem safeFuel_stable (k l : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (ω : Ω) (hω : D.conditional h ω ≠ 0)
    (hk : D.cap ≤ D.clock h + k) (hl : D.cap ≤ D.clock h + l) :
    D.safeFuel k h ω = D.safeFuel l h ω := by
  induction k generalizing l h with
  | zero =>
    have hs := D.cap_stopped h (by simpa using hk)
    rw [D.safeFuel_of_stopped 0 h ω hs, D.safeFuel_of_stopped l h ω hs]
  | succ k ih =>
    by_cases hs : D.stopped h = true
    · rw [D.safeFuel_of_stopped _ h ω hs, D.safeFuel_of_stopped _ h ω hs]
    have hs' := Bool.eq_false_iff.mpr hs
    cases l with
    | zero =>
      exact (hs (D.cap_stopped h (by simpa using hl))).elim
    | succ l =>
      have hj := D.next_supported h ω hω
      have hprog := D.progress h _ hh hs' hj
      simp only [safeFuel, hs', Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · exact ih l (D.next h ω) (D.child_nonnull h _ hh hj)
          (D.path_supported_child h hh ω hω) (by omega) (by omega)

/-- Actual avoidance up to the visible stopping rule. Chronology makes this horizon sufficient. -/
def safe (h : Fin M) (ω : Ω) : Bool := D.safeFuel (D.cap + 1) h ω

/-- The actual full-path avoidance law up to the visible stopping rule. -/
noncomputable def safeLaw (h : Fin M) : PMF Bool := (D.conditional h).map (D.safe h)

/-- Exact full-path stopping semantics: stop safely, fail at target, otherwise continue. -/
theorem safe_unfold (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (ω : Ω) (hω : D.conditional h ω ≠ 0) :
    D.safe h ω = if D.stopped h then true else
      if D.kind h (D.next h ω) = .target then false else D.safe (D.next h ω) ω := by
  unfold safe
  rw [safeFuel]
  split
  · rfl
  · split
    · rfl
    · exact D.safeFuel_stable D.cap (D.cap + 1) (D.next h ω)
        (D.child_nonnull h _ hh (D.next_supported h ω hω)) ω
        (D.path_supported_child h hh ω hω) (by omega) (by omega)

/-- The actual conditional avoidance probability is bounded by the remaining-count potential. -/
theorem potential_le_safe_probability (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    CompetingHazards.potential A (D.remaining h) ≤ (D.safeLaw h true).toReal :=
  D.potential_le_successFuel hA (D.cap + 1) h hh

/-- Actual target-before-stop failure bound. -/
theorem safe_failure_le_one_sub_potential (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    (D.safeLaw h false).toReal ≤ 1 - CompetingHazards.potential A (D.remaining h) :=
  D.failureFuel_le_one_sub_potential hA (D.cap + 1) h hh

/-- At most two remaining empty destinations give the uniform actual safe probability. -/
theorem two_empty_le_safe_probability (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : D.remaining h ≤ 2) :
    CompetingHazards.potential A 2 ≤ (D.safeLaw h true).toReal :=
  D.two_empty_le_successFuel hA (D.cap + 1) h hh hk

/-- Event form of the actual stopping-rule failure bound. -/
theorem safe_failure_event_le (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    (eventMass (D.conditional h) {ω | D.safe h ω = false}).toReal ≤
      1 - CompetingHazards.potential A (D.remaining h) :=
  D.failure_eventFuel_le hA (D.cap + 1) h hh

/-- Uniform two-empty failure event bound for downstream return-event inclusions. -/
theorem two_empty_failure_event_le (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : D.remaining h ≤ 2) :
    (eventMass (D.conditional h) {ω | D.safe h ω = false}).toReal ≤
      1 - CompetingHazards.potential A 2 := by
  have hb := D.safe_failure_event_le hA h hh
  have hp : CompetingHazards.potential A 2 ≤ CompetingHazards.potential A (D.remaining h) :=
    pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith))
      ((inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)) hk
  linarith

/-- Events contained in failure on the conditional support inherit the failure bound. -/
theorem event_le_failure (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (E : Set Ω)
    (hE : ∀ ω, D.conditional h ω ≠ 0 → ω ∈ E → D.safe h ω = false) :
    (eventMass (D.conditional h) E).toReal ≤
      1 - CompetingHazards.potential A (D.remaining h) := by
  have hm : eventMass (D.conditional h) E ≤
      eventMass (D.conditional h) {ω | D.safe h ω = false} := by
    apply ENNReal.tsum_le_tsum
    intro ω
    by_cases hω : D.conditional h ω = 0
    · simp only [Set.indicator_apply]
      split_ifs <;> simp [hω]
    by_cases he : ω ∈ E
    · have hf : ω ∈ {ω | D.safe h ω = false} := hE ω hω he
      rw [Set.indicator_of_mem he, Set.indicator_of_mem hf]
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  exact (ENNReal.toReal_mono (eventMass_ne_top _ _) hm).trans
    (D.safe_failure_event_le hA h hh)

/-- A return event excluded by safe paths has the uniform two-empty failure bound. -/
theorem two_empty_event_le_failure (hA : 0 ≤ A) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : D.remaining h ≤ 2) (E : Set Ω)
    (hE : ∀ ω, D.conditional h ω ≠ 0 → ω ∈ E → D.safe h ω = false) :
    (eventMass (D.conditional h) E).toReal ≤ 1 - CompetingHazards.potential A 2 := by
  have hb := D.event_le_failure hA h hh E hE
  have hp : CompetingHazards.potential A 2 ≤ CompetingHazards.potential A (D.remaining h) :=
    pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith))
      ((inv_le_one₀ (by linarith : 0 < A + 1)).mpr (by linarith)) hk
  linarith

end Process
end TieredMatching.CompetingProcess
