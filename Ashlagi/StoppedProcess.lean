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

public import Ashlagi.FiniteConditioning
public import Ashlagi.StoppedHazards

/-! # Actual finite observation processes and stopped exponential bounds

Literal prefix-event refinement disintegrates the original full-path law. Finite recursion
bounds the actual count law by the stopped-hazard potential. Chronological reward agreement
  accounts for every raw attempt,
including between compressed held-episode boundaries.
-/

@[expose] public section

namespace Ashlagi.StoppedProcess

open MeasureTheory FiniteConditioning StoppedHazards
open scoped ENNReal

/-- Conditional laws can be compared on their support; null branches have zero bind weight. -/
theorem bind_congr_support {α β : Type*} (μ : PMF α) (f g : α → PMF β)
    (h : ∀ a, μ a ≠ 0 → f a = g a) : μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : μ a = 0
  · simp only [ha, zero_mul]
  · rw [h a ha]

/-- Exact nested conditioning on a nonnull intersection. The second event is observed under
the first conditional law; its result is the original law restricted to the intersection. -/
theorem condition_inter {Ω : Type*} (μ : PMF Ω) (S T : Set Ω)
    (hj : eventMass μ (S ∩ T) ≠ 0) :
    condition (condition μ S) T = condition μ (S ∩ T) := by
  classical
  ext a
  apply (ENNReal.mul_right_inj hj (eventMass_ne_top μ (S ∩ T))).mp
  rw [← eventMass_mul_conditional_event μ S T, mul_assoc,
    eventMass_mul_condition, eventMass_mul_conditional_event]
  rw [eventMass_mul_condition]
  by_cases hs : a ∈ S <;> by_cases ht : a ∈ T <;>
    simp only [Set.indicator_apply, Set.mem_inter_iff, hs, ht, and_true, and_false,
      ite_true, ite_false, mul_zero, eventMass_mul_condition]

/-- A visible-history boundary process under its original finite full-path probability law.
Every branch is an observation of that same path. No transition kernel or tree is supplied. -/
structure Process (Ω : Type*) (M : ℕ) (p q : ℝ) where
  law : PMF Ω
  event : Fin M → Set Ω
  phase : Fin M → Phase
  stopped : Fin M → Bool
  attempt : Fin M → Bool
  next : Fin M → Ω → Fin M
  accepted : Fin M → Fin M → Bool
  returns : Fin M → Fin M → Bool
  /-- Every nonnull successor fiber is literally its parent's next-observation fiber. -/
  refines : ∀ h j,
    eventMass law (event h) ≠ 0 →
    ((condition law (event h)).map (next h)) j ≠ 0 →
    event j = event h ∩ {ω | next h ω = j}
  /-- An absorbed branch has no further counted attempts. -/
  absorbed_stopped : ∀ h, phase h = .absorbed → stopped h = true
  /-- Successor phases are determined by the visible acceptance/return observation. -/
  phase_next : ∀ h j,
    eventMass law (event h) ≠ 0 → stopped h = false →
    ((condition law (event h)).map (next h)) j ≠ 0 →
    phase j = match phase h with
      | .free => if attempt h then (if accepted h j then .held else .free) else .free
      | .held => if returns h j then .free else .absorbed
      | .absorbed => .absorbed
  acceptance : ∀ h, eventMass law (event h) ≠ 0 → stopped h = false →
    phase h = .free → attempt h = true →
    p ≤ branchMass ((condition law (event h)).map (next h)) (accepted h)
  regeneration : ∀ h, eventMass law (event h) ≠ 0 → stopped h = false →
    phase h = .held →
    branchMass ((condition law (event h)).map (next h)) (returns h) ≤ 1 - q

namespace Process

variable {Ω : Type*} {M : ℕ} {p q : ℝ} (D : Process Ω M p q)

/-- The actual path law conditioned only on its visible history. -/
noncomputable def conditional (h : Fin M) : PMF Ω := condition D.law (D.event h)

/-- Distribution of the next visible boundary, derived from the original path law. -/
noncomputable def transition (h : Fin M) : PMF (Fin M) :=
  (D.conditional h).map (D.next h)

/-- Every nonnull branch has a nonnull original prefix event. -/
theorem child_nonnull (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) : eventMass D.law (D.event j) ≠ 0 := by
  rw [D.refines h j hh hj, ← eventMass_mul_conditional_event,
    eventMass_observation_fiber]
  exact mul_ne_zero hh hj

/-- A boundary branch conditions on exactly its child prefix event under the original law. -/
theorem condition_next (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) :
    condition (D.conditional h) {ω | D.next h ω = j} = D.conditional j := by
  rw [conditional, conditional, D.refines h j hh hj]
  exact condition_inter D.law _ _ (by
    rw [← D.refines h j hh hj]
    exact D.child_nonnull h j hh hj)

/-- Finite tower identity over the actual boundary observation; null branches are harmless. -/
theorem boundary_disintegration (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (D.transition h).bind D.conditional = D.conditional h := by
  calc
    _ = (D.transition h).bind
        (fun j ↦ condition (D.conditional h) {ω | D.next h ω = j}) := by
      apply bind_congr_support
      intro j hj
      exact (D.condition_next h j hh hj).symm
    _ = D.conditional h := bind_condition_eq _ _

/-- Whether the current visible boundary counts one designated free proposal. -/
def reward (h : Fin M) : ℕ := if D.phase h = .free ∧ D.attempt h = true then 1 else 0

/-- The actual finite-horizon sum of designated attempt rewards along boundary observations.
The recursion follows the single underlying path; it draws no new random variables. -/
def countFuel : ℕ → Fin M → Ω → ℕ
  | 0, _, _ => 0
  | k + 1, h, ω => if D.stopped h then 0 else D.reward h + countFuel k (D.next h ω) ω

/-- Equality of mapped laws needs equality only on points with positive mass. -/
theorem map_congr_support {α β : Type*} (μ : PMF α) (f g : α → β)
    (h : ∀ a, μ a ≠ 0 → f a = g a) : μ.map f = μ.map g := by
  apply bind_congr_support
  intro a ha
  change PMF.pure (f a) = PMF.pure (g a)
  rw [h a ha]

/-- A realized nonnull child prefix fixes its parent's boundary observation. -/
theorem child_support_next (h j : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hj : D.transition h j ≠ 0) (ω : Ω) (hω : D.conditional j ω ≠ 0) : D.next h ω = j := by
  have hs : ω ∈ (condition D.law (D.event j)).support := hω
  rw [support_condition D.law (D.event j) (D.child_nonnull h j hh hj)] at hs
  rw [D.refines h j hh hj] at hs
  exact hs.1.2

/-- Actual pathwise counts satisfy total expectation over boundary prefix observations.
The identity is proved from disintegration and support refinement, not assumed as a recurrence. -/
theorem count_map_succ (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (hs : D.stopped h = false) :
    (D.conditional h).map (D.countFuel (k + 1) h) =
      (D.transition h).bind fun j ↦
        ((D.conditional j).map (D.countFuel k j)).map (fun c ↦ D.reward h + c) := by
  conv_lhs => rw [← D.boundary_disintegration h hh]
  rw [PMF.map_bind]
  apply bind_congr_support
  intro j hj
  rw [PMF.map_comp]
  apply map_congr_support
  intro ω hω
  simp only [countFuel, hs, Bool.false_eq_true, ↓reduceIte, Function.comp_apply,
    D.child_support_next h j hh hj ω hω]

/-- The actual transition's child phase, including compressed held exits. -/
def successorPhase (h j : Fin M) : Phase := match D.phase h with
  | .free => if D.attempt h then (if D.accepted h j then .held else .free) else .free
  | .held => if D.returns h j then .free else .absorbed
  | .absorbed => .absorbed


/-- Nonnegative expectation comparisons ignore branches of zero probability. -/
theorem expectation_mono_support {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a, μ a ≠ 0 → f a ≤ g a) : expectation μ f ≤ expectation μ g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : μ a = 0
  · simp only [ha, zero_mul, le_refl]
  · exact mul_le_mul_right (h a ha) (μ a)

/-- Adding a fixed path reward multiplies the probability generating function by its power. -/
theorem pgf_map_add (z : ℝ≥0∞) (μ : PMF ℕ) (r : ℕ) :
    pgf z (μ.map (fun c ↦ r + c)) = z ^ r * pgf z μ := by
  rw [pgf, expectation_map]
  simp only [pow_add, expectation_const_mul]
  rfl

/-- Exact PGF tower identity derived from the actual finite path law. -/
theorem pgf_count_succ (z : ℝ≥0∞) (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hs : D.stopped h = false) :
    pgf z ((D.conditional h).map (D.countFuel (k + 1) h)) =
      z ^ D.reward h * expectation (D.transition h)
        (fun j ↦ pgf z ((D.conditional j).map (D.countFuel k j))) := by
  rw [D.count_map_succ k h hh hs, pgf, expectation_bind]
  change expectation (D.transition h) (fun j ↦ pgf z
    (((D.conditional j).map (D.countFuel k j)).map (fun c ↦ D.reward h + c))) = _
  simp only [pgf_map_add, expectation_const_mul]

/-- Backward induction bounds the actual conditional count PGF by the current potential.
The only probabilistic assumptions are the stated current-history local hazards. -/
theorem pgf_count_le (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1) (k : ℕ)
    (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    pgf (ENNReal.ofReal (Real.exp (theta p q)))
      ((D.conditional h).map (D.countFuel k h)) ≤ ENNReal.ofReal (potential q (D.phase h)) := by
  induction k generalizing h with
  | zero =>
    change pgf _ ((D.conditional h).map (fun _ ↦ 0)) ≤ _
    rw [show (fun _ : Ω ↦ (0 : ℕ)) = Function.const Ω 0 from rfl, PMF.map_const]
    simpa only [pgf, expectation_pure, pow_zero, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (one_le_potential hq (D.phase h))
  | succ k ih =>
    by_cases hs : D.stopped h = true
    · have hc : D.countFuel (k + 1) h = Function.const Ω 0 := by
        funext ω
        simp only [countFuel, hs, ↓reduceIte, Function.const_apply]
      rw [hc, PMF.map_const]
      simpa only [pgf, expectation_pure, pow_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (one_le_potential hq (D.phase h))
    have hs' := Bool.eq_false_iff.mpr hs
    rw [D.pgf_count_succ _ k h hh hs']
    have hchild : expectation (D.transition h)
        (fun j ↦ pgf (ENNReal.ofReal (Real.exp (theta p q)))
          ((D.conditional j).map (D.countFuel k j))) ≤
        expectation (D.transition h)
          (fun j ↦ ENNReal.ofReal (potential q (D.successorPhase h j))) := by
      apply expectation_mono_support
      intro j hj
      have heq : D.phase j = D.successorPhase h j := D.phase_next h j hh hs' hj
      rw [← heq]
      exact ih j (D.child_nonnull h j hh hj)
    apply (mul_le_mul_right hchild _).trans
    cases he : D.phase h with
    | free =>
      by_cases ha : D.attempt h = true
      · simp only [reward, he, ha, and_self, ↓reduceIte, pow_one, successorPhase]
        rw [expectation_ofReal _ _ (fun j ↦ zero_le_one.trans (one_le_potential hq _)),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, weighted_attempt_potential]
        exact ENNReal.ofReal_le_ofReal
          (free_bellman_le hp hq hq0 (D.acceptance h hh hs' he ha))
      · simp only [reward, he, ha, and_false, ↓reduceIte, pow_zero, one_mul,
          successorPhase, Bool.false_eq_true, expectation_const]
        exact le_rfl
    | held =>
      have hnf : Phase.held ≠ Phase.free := by decide
      simp only [reward, he, hnf, false_and, ↓reduceIte, pow_zero, one_mul, successorPhase]
      rw [expectation_ofReal _ _ (fun j ↦ zero_le_one.trans (one_le_potential hq _)),
        weighted_episode_potential]
      exact ENNReal.ofReal_le_ofReal (held_bellman_le (D.regeneration h hh hs' he))
    | absorbed => exact False.elim (hs (D.absorbed_stopped h he))
/-- The finite-horizon stopped exponential moment is bounded by its free/held/absorbed
potential. In particular the initial phase may already be held. -/
theorem exponential_moment_le_potential (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫⁻ k, ENNReal.ofReal (Real.exp (theta p q * (k : ℝ))) ∂((D.conditional h).map (D.countFuel k
      h)).toMeasure) ≤
      ENNReal.ofReal (potential q (D.phase h)) := by
  rw [← pgf_exp_eq_lintegral]
  exact D.pgf_count_le hp hq0 hq k h hh

/-- Every possible initial phase has stopped exponential moment at most two. -/
theorem exponential_moment_le_two (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫⁻ k, ENNReal.ofReal (Real.exp (theta p q * (k : ℝ))) ∂((D.conditional h).map (D.countFuel k
      h)).toMeasure) ≤ 2 := by
  have hv : potential q (D.phase h) ≤ 2 := by cases D.phase h <;> dsimp [potential] <;> linarith
  exact (D.exponential_moment_le_potential hp hq0 hq k h hh).trans
    (by simpa using ENNReal.ofReal_le_ofReal hv)

/-- Exponential Markov gives a quantitative tail for the actual finite path count law. -/
theorem count_tail_le (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) (threshold : ℝ) :
    ((D.conditional h).map (D.countFuel k h)).toMeasure {k : ℕ | threshold ≤ (k : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-theta p q * threshold)) := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hne : ENNReal.ofReal (Real.exp (theta p q * threshold)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hm : Measurable (fun k : ℕ ↦ ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))) :=
    Measurable.of_discrete
  have hmark := meas_ge_le_lintegral_div (μ := ((D.conditional h).map (D.countFuel k
    h)).toMeasure) hm.aemeasurable
    hne ENNReal.ofReal_ne_top
  have hsub : {k : ℕ | threshold ≤ (k : ℝ)} ⊆
      {k : ℕ | ENNReal.ofReal (Real.exp (theta p q * threshold)) ≤
        ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))} := by
    intro k hk
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hθ.le))
  calc
    _ ≤ ((D.conditional h).map (D.countFuel k h)).toMeasure {k : ℕ |
        ENNReal.ofReal (Real.exp (theta p q * threshold)) ≤
          ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))} := measure_mono hsub
    _ ≤ _ := hmark
    _ ≤ 2 / ENNReal.ofReal (Real.exp (theta p q * threshold)) :=
      ENNReal.div_le_div_right (D.exponential_moment_le_two hp hq0.le hq k h hh) _
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      simp only [div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- The simpler hazard-product tail follows from `theta ≥ p*q/2` at nonnegative thresholds. -/
theorem count_tail_le_half_mul (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (threshold : ℝ) (ht : 0 ≤ threshold) :
    ((D.conditional h).map (D.countFuel k h)).toMeasure {k : ℕ | threshold ≤ (k : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-(p * q / 2) * threshold)) := by
  apply (D.count_tail_le hp0 hp hq0 hq k h hh threshold).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact theta_ge_half_mul hp hq hq0.le

/-- The moment bound proves integrability of the actual real exponential, rather than
silently using the default value of an undefined real integral. -/
theorem integrable_exponential_count (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    Integrable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) ((D.conditional h).map (D.countFuel k
      h)).toMeasure := by
  have hm : Measurable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) := Measurable.of_discrete
  apply (lintegral_ofReal_ne_top_iff_integrable
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k : ℕ ↦ (Real.exp_pos (theta p q * (k : ℝ))).le)).mp
  exact (lt_of_le_of_lt (D.exponential_moment_le_two hp hq0 hq k h hh) (by norm_num)).ne

/-- Real-valued expected exponential form of the stopped-process bound. -/
theorem integral_exponential_count_le_two (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫ k : ℕ, Real.exp (theta p q * (k : ℝ)) ∂((D.conditional h).map (D.countFuel k h)).toMeasure)
      ≤ 2 := by
  have hm : Measurable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) := Measurable.of_discrete
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun k : ℕ ↦ (Real.exp_pos (theta p q * (k : ℝ))).le)
    hm.aestronglyMeasurable]
  simpa using ENNReal.toReal_mono (by norm_num)
    (D.exponential_moment_le_two hp hq0 hq k h hh)

/-- The designated count is integrable when both hazards are positive. -/
theorem integrable_count (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) ((D.conditional h).map (D.countFuel k h)).toMeasure := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hexp := (D.integrable_exponential_count hp hq0.le hq k h hh).div_const (theta p q)
  apply hexp.mono' Measurable.of_discrete.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  apply (le_div_iff₀ hθ).mpr
  have hbound := Real.add_one_le_exp (theta p q * (k : ℝ))
  nlinarith

/-- The same finite-horizon argument yields the geometric-scale mean without independence of
free-bout costs and regeneration outcomes. -/
theorem integral_count_le_inv_theta (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫ k : ℕ, (k : ℝ) ∂((D.conditional h).map (D.countFuel k h)).toMeasure) ≤ (theta p q)⁻¹ := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hcount := D.integrable_count hp0 hp hq0 hq k h hh
  have hexp := D.integrable_exponential_count hp hq0.le hq k h hh
  have hlinear := (hcount.const_mul (theta p q)).add
    (integrable_const (μ := ((D.conditional h).map (D.countFuel k h)).toMeasure) (1 : ℝ))
  have hbound := integral_mono hlinear hexp
    (fun k ↦ Real.add_one_le_exp (theta p q * (k : ℝ)))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hcount.const_mul (theta p q)) (integrable_const 1), integral_const_mul]
    at hbound
  have hmgf := D.integral_exponential_count_le_two hp hq0.le hq k h hh
  have hprod : (∫ k : ℕ, (k : ℝ) ∂((D.conditional h).map (D.countFuel k h)).toMeasure) * theta p q
    ≤ 1 := by
    simp only [integral_const, probReal_univ, one_smul] at hbound
    nlinarith
  simpa only [one_div] using (le_div_iff₀ hθ).mpr hprod

/-- Explicit mean bound in terms of the two conditional hazard constants. -/
theorem integral_count_le_two_div_mul (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫ k : ℕ, (k : ℝ) ∂((D.conditional h).map (D.countFuel k h)).toMeasure) ≤ 2 / (p * q) := by
  apply (D.integral_count_le_inv_theta hp0 hp hq0 hq k h hh).trans
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hpq : 0 < p * q := mul_pos hp0 hq0
  apply (le_div_iff₀ hpq).mpr
  have hbound : (p * q / 2) * (theta p q)⁻¹ ≤ 1 := by
    calc
      _ ≤ theta p q * (theta p q)⁻¹ :=
        mul_le_mul_of_nonneg_right (theta_ge_half_mul hp hq hq0.le) (inv_pos.mpr hθ).le
      _ = 1 := mul_inv_cancel₀ hθ.ne'
  nlinarith

/-- Exponential PGFs of actual mapped counts are expectations on the original path space. -/
theorem pgf_exponential_map (μ : PMF Ω) (F : Ω → ℕ) (θ : ℝ) :
    pgf (ENNReal.ofReal (Real.exp θ)) (μ.map F) =
      expectation μ (fun ω ↦ ENNReal.ofReal (Real.exp (θ * (F ω : ℝ)))) := by
  rw [pgf, expectation_map]
  congr 1
  funext ω
  rw [mul_comm θ, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le]

/-- Actual path-space exponential expectation, rather than a supplied reward-tree bound. -/
theorem path_exponential_expectation_le_two (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (k : ℕ) (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    expectation (D.conditional h)
      (fun ω ↦ ENNReal.ofReal (Real.exp (theta p q * (D.countFuel k h ω : ℝ)))) ≤ 2 := by
  rw [← pgf_exponential_map]
  have hv : potential q (D.phase h) ≤ 2 := by cases D.phase h <;> dsimp [potential] <;> linarith
  exact (D.pgf_count_le hp hq0 hq k h hh).trans
    (by simpa using ENNReal.ofReal_le_ofReal hv)

/-- The mass of the entire original path space is one. -/
theorem eventMass_univ (μ : PMF Ω) : eventMass μ Set.univ = 1 := by
  simpa only [eventMass, Set.indicator_univ] using μ.tsum_coe

/-- A root history carrying no information has the original path law. -/
theorem conditional_root (h : Fin M) (he : D.event h = Set.univ) :
    D.conditional h = D.law := by
  ext ω
  have hid := eventMass_mul_condition D.law (D.event h) ω
  simpa only [conditional, he, eventMass_univ, one_mul, Set.indicator_univ] using hid

/-- A supported actual path induces a nonnull next boundary branch. -/
theorem next_support (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0)
    (ω : Ω) (hω : D.law ω ≠ 0) (he : ω ∈ D.event h) :
    D.transition h (D.next h ω) ≠ 0 := by
  have hs : ω ∈ (D.conditional h).support := by
    rw [conditional, support_condition D.law (D.event h) hh]
    exact ⟨he, hω⟩
  exact (PMF.mem_support_map_iff (D.next h) (D.conditional h) (D.next h ω)).mpr ⟨ω, hs, rfl⟩

/-- Chronological interpretation of a boundary process. `rawAttempt` is the actual designated
attempt indicator on the public raw clock. Boundary reward agreement counts the *whole*
interval to the next boundary; hence a compressed held episode cannot discard attempts. -/
structure Chronology where
  horizon : ℕ
  clock : Fin M → ℕ
  clock_le : ∀ h, clock h ≤ horizon
  rawAttempt : ℕ → Ω → Bool
  progress : ∀ h j, eventMass D.law (D.event h) ≠ 0 → D.stopped h = false →
    D.transition h j ≠ 0 → clock h < clock j
  boundary_reward : ∀ h ω, D.law ω ≠ 0 → ω ∈ D.event h → D.stopped h = false →
    (∑ t ∈ Finset.Ico (clock h) (clock (D.next h ω)),
      if rawAttempt t ω then 1 else 0) = D.reward h
  stopped_reward : ∀ h ω, D.law ω ≠ 0 → ω ∈ D.event h → D.stopped h = true →
    (∑ t ∈ Finset.Ico (clock h) horizon, if rawAttempt t ω then 1 else 0) = 0

namespace Chronology

variable {D}
variable (T : D.Chronology)

/-- The actual number of remaining raw attempts, with no omitted clock intervals. -/
def rawCount (h : Fin M) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.Ico (T.clock h) T.horizon, if T.rawAttempt t ω then 1 else 0

/-- Strict boundary progress makes enough finite recursion count exactly every raw attempt. -/
theorem countFuel_eq_rawCount (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : T.horizon - T.clock h ≤ k)
    (ω : Ω) (hω : D.law ω ≠ 0) (he : ω ∈ D.event h) :
    D.countFuel k h ω = T.rawCount h ω := by
  induction k generalizing h with
  | zero =>
    have hc : T.clock h = T.horizon := by have := T.clock_le h; omega
    simp only [countFuel, rawCount, hc, Finset.Ico_self, Finset.sum_empty]
  | succ k ih =>
    by_cases hs : D.stopped h = true
    · simp only [countFuel, hs, ↓reduceIte]
      exact (T.stopped_reward h ω hω he hs).symm
    have hs' := Bool.eq_false_iff.mpr hs
    have hj := D.next_support h hh ω hω he
    have hjj := D.child_nonnull h (D.next h ω) hh hj
    have hclock := T.progress h (D.next h ω) hh hs' hj
    have hchild : ω ∈ D.event (D.next h ω) := by
      rw [D.refines h (D.next h ω) hh hj]
      exact ⟨he, rfl⟩
    have hroom : T.horizon - T.clock (D.next h ω) ≤ k := by omega
    rw [countFuel, ite_eq_right hs, ih _ hjj hroom hchild]
    rw [← T.boundary_reward h ω hω he hs']
    exact Finset.sum_Ico_consecutive (fun t ↦ if T.rawAttempt t ω then 1 else 0)
      hclock.le (T.clock_le _)

/-- Exact equality of the actual raw-attempt law and the finite boundary recursion law. -/
theorem map_rawCount (k : ℕ) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) (hk : T.horizon - T.clock h ≤ k) :
    (D.conditional h).map (T.rawCount h) = (D.conditional h).map (D.countFuel k h) := by
  apply map_congr_support
  intro ω hω
  have hs : ω ∈ (D.conditional h).support := hω
  rw [conditional, support_condition D.law (D.event h) hh] at hs
  exact (T.countFuel_eq_rawCount k h hh hk ω hs.2 hs.1).symm

/-- The actual raw-attempt exponential moment has the stopped potential bound. -/
theorem raw_exponential_moment_le_two (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫⁻ c, ENNReal.ofReal (Real.exp (theta p q * (c : ℝ)))
      ∂((D.conditional h).map (T.rawCount h)).toMeasure) ≤ 2 := by
  rw [T.map_rawCount T.horizon h hh (Nat.sub_le _ _)]
  exact D.exponential_moment_le_two hp hq0 hq T.horizon h hh

/-- The actual raw-attempt tail is bounded without independent survival labels. -/
theorem raw_count_tail_le (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) (threshold : ℝ) :
    ((D.conditional h).map (T.rawCount h)).toMeasure {c : ℕ | threshold ≤ (c : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-theta p q * threshold)) := by
  rw [T.map_rawCount T.horizon h hh (Nat.sub_le _ _)]
  exact D.count_tail_le hp0 hp hq0 hq T.horizon h hh threshold

/-- The actual raw-attempt mean has geometric scale `2/(p*q)`. -/
theorem raw_integral_count_le_two_div_mul (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1) (h : Fin M)
    (hh : eventMass D.law (D.event h) ≠ 0) :
    (∫ c : ℕ, (c : ℝ) ∂((D.conditional h).map (T.rawCount h)).toMeasure) ≤ 2 / (p * q) := by
  rw [T.map_rawCount T.horizon h hh (Nat.sub_le _ _)]
  exact D.integral_count_le_two_div_mul hp0 hp hq0 hq T.horizon h hh

/-- Exponential expectation on the actual original path variables, conditionally on a prefix. -/
theorem raw_path_exponential_expectation_le_two (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (h : Fin M) (hh : eventMass D.law (D.event h) ≠ 0) :
    expectation (D.conditional h)
      (fun ω ↦ ENNReal.ofReal (Real.exp (theta p q * (T.rawCount h ω : ℝ)))) ≤ 2 := by
  rw [← pgf_exponential_map, T.map_rawCount T.horizon h hh (Nat.sub_le _ _)]
  have hv : potential q (D.phase h) ≤ 2 := by cases D.phase h <;> dsimp [potential] <;> linarith
  exact (D.pgf_count_le hp hq0 hq T.horizon h hh).trans
    (by simpa using ENNReal.ofReal_le_ofReal hv)

/-- At an uninformative root, the actual full-path law satisfies the exponential, mean, and
tail bounds. The supplied data contain only visible local hazards and deterministic raw-clock
accounting; a tree witness or moment recurrence is not an input. -/
theorem raw_root_bounds (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    (h : Fin M) (he : D.event h = Set.univ) :
    expectation D.law
      (fun ω ↦ ENNReal.ofReal (Real.exp (theta p q * (T.rawCount h ω : ℝ)))) ≤ 2 ∧
    (∫ c : ℕ, (c : ℝ) ∂(D.law.map (T.rawCount h)).toMeasure) ≤ 2 / (p * q) ∧
    ∀ threshold : ℝ, (D.law.map (T.rawCount h)).toMeasure {c : ℕ | threshold ≤ (c : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-theta p q * threshold)) := by
  have hh : eventMass D.law (D.event h) ≠ 0 := by rw [he, eventMass_univ]; norm_num
  have hc := D.conditional_root h he
  exact ⟨hc ▸ T.raw_path_exponential_expectation_le_two hp hq0.le hq h hh,
    hc ▸ T.raw_integral_count_le_two_div_mul hp0 hp hq0 hq h hh,
    fun threshold ↦ hc ▸ T.raw_count_tail_le hp0 hp hq0 hq h hh threshold⟩


end Chronology

end Process

end Ashlagi.StoppedProcess
