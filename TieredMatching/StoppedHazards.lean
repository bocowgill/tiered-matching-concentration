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

public import Mathlib

/-! # Finite stopped two-phase exponential moment bounds

Every node may use its own finite transition PMF. Held episodes are compressed to their first
return to the free phase or absorption. The resulting finite reward tree has no independent
survival marks, and its exponential moment is bounded by backward induction.
-/

@[expose] public section

namespace TieredMatching.StoppedHazards

open MeasureTheory
open scoped ENNReal NNReal

/-- A nonnegative expectation under a discrete probability law. -/
noncomputable def expectation {α : Type*} (law : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, law a * f a

/-- Total expectation for arbitrary discrete conditional laws. -/
theorem expectation_bind {α β : Type*} (law : PMF α) (next : α → PMF β)
    (f : β → ℝ≥0∞) :
    expectation (law.bind next) f = expectation law (fun a ↦ expectation (next a) f) := by
  unfold expectation
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc, ENNReal.tsum_mul_left]

/-- A point law has the expected value prescribed at its sole outcome. -/
theorem expectation_pure {α : Type*} (a : α) (f : α → ℝ≥0∞) :
    expectation (PMF.pure a) f = f a := by
  classical
  simp [expectation, PMF.pure_apply]

/-- Pushing a probability law forward composes its tested reward function. -/
theorem expectation_map {α β : Type*} (law : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expectation (law.map g) f = expectation law (fun a ↦ f (g a)) := by
  simp only [PMF.map, expectation_bind, Function.comp_apply, expectation_pure]

/-- Probability generating function, also defined at positive values above one. -/
noncomputable def pgf (z : ℝ≥0∞) (law : PMF ℕ) : ℝ≥0∞ :=
  expectation law (fun k ↦ z ^ k)

/-- Adding one counted attempt multiplies the generating function by its base. -/
theorem pgf_map_succ (z : ℝ≥0∞) (law : PMF ℕ) :
    pgf z (law.map Nat.succ) = z * pgf z law := by
  rw [pgf, expectation_map]
  calc
    expectation law (fun k ↦ z ^ k.succ) = ∑' k, (law k * z ^ k) * z := by
      simp only [expectation, pow_succ, mul_assoc]
    _ = z * pgf z law := by
      rw [ENNReal.tsum_mul_right, mul_comm]
      rfl

/-- The real masses of a finite PMF sum to one. -/
theorem sum_real_mass {n : ℕ} (law : PMF (Fin n)) : ∑ i, (law i).toReal = 1 := by
  have hsum : ∑ i, law i = 1 := by simpa only [tsum_fintype] using law.tsum_coe
  rw [← ENNReal.toReal_sum (fun i _ ↦ law.apply_ne_top i), hsum]
  rfl

/-- Mass assigned to a designated Boolean branch. -/
noncomputable def branchMass {n : ℕ} (law : PMF (Fin n)) (selected : Fin n → Bool) : ℝ :=
  ∑ i, if selected i then (law i).toReal else 0

/-- The designated participant's three phases. -/
inductive Phase where
  | free
  | held
  | absorbed
  deriving DecidableEq

/-- The superharmonic potential used for the stopped process. -/
def potential (q : ℝ) : Phase → ℝ
  | .free => 2
  | .held => 2 - q
  | .absorbed => 1

/-- A finite history-dependent stopped process. An attempt counts one unit. An idle step
counts none. A held episode ends at its first return to free or absorption and counts none.
Each constructor has its own PMF, so no independence between different episodes is imposed. -/
inductive Tree (p q : ℝ) : Phase → Type
  | stop (phase : Phase) : Tree p q phase
  | idle {n : ℕ} (law : PMF (Fin n))
      (child : Fin n → Tree p q .free) : Tree p q .free
  | attempt {n : ℕ} (law : PMF (Fin n)) (accepted : Fin n → Bool)
      (hazard : p ≤ branchMass law accepted)
      (child : (i : Fin n) → Tree p q (if accepted i then .held else .free)) : Tree p q .free
  | episode {n : ℕ} (law : PMF (Fin n)) (returns : Fin n → Bool)
      (regeneration : branchMass law returns ≤ 1 - q)
      (child : (i : Fin n) → Tree p q (if returns i then .free else .absorbed)) : Tree p q .held

/-- The actual probability law of the tree's total counted attempts. -/
noncomputable def countLaw {p q : ℝ} : {phase : Phase} → Tree p q phase → PMF ℕ
  | _, .stop _ => PMF.pure 0
  | _, .idle law child => law.bind fun i ↦ countLaw (child i)
  | _, .attempt law _ _ child => law.bind fun i ↦ (countLaw (child i)).map Nat.succ
  | _, .episode law _ _ child => law.bind fun i ↦ countLaw (child i)

/-- A finite upper bound on the number of remaining tree transitions. Compressed held
episodes may represent several global raw steps, so this bound counts episode nodes. -/
def horizon {p q : ℝ} : {phase : Phase} → Tree p q phase → ℕ
  | _, .stop _ => 0
  | _, .idle _ child => 1 + Finset.univ.sup (fun i ↦ horizon (child i))
  | _, .attempt _ _ _ child => 1 + Finset.univ.sup (fun i ↦ horizon (child i))
  | _, .episode _ _ _ child => 1 + Finset.univ.sup (fun i ↦ horizon (child i))

/-- The count law is supported on its finite horizon. This makes the finite nature of the
backward induction explicit, independently of the later moment bound. -/
theorem countLaw_support_le_horizon {p q : ℝ} {phase : Phase} (tree : Tree p q phase) :
    ∀ k ∈ (countLaw tree).support, k ≤ horizon tree := by
  induction tree with
  | stop phase =>
    intro k hk
    have hk0 : k = 0 := by
      simpa only [countLaw, PMF.support_pure, Set.mem_singleton_iff] using hk
    subst k
    exact le_rfl
  | idle law child ih =>
    intro k hk
    obtain ⟨i, _, hchild⟩ := (PMF.mem_support_bind_iff law _ k).mp hk
    have hi := ih i k hchild
    have hs : horizon (child i) ≤ Finset.univ.sup (fun j ↦ horizon (child j)) :=
      Finset.le_sup (f := fun j ↦ horizon (child j)) (Finset.mem_univ i)
    change k ≤ 1 + Finset.univ.sup (fun j ↦ horizon (child j))
    omega
  | attempt law accepted hazard child ih =>
    intro k hk
    obtain ⟨i, _, hmap⟩ := (PMF.mem_support_bind_iff law _ k).mp hk
    obtain ⟨j, hj, hsucc⟩ := (PMF.mem_support_map_iff Nat.succ (countLaw (child i)) k).mp hmap
    have hi := ih i j hj
    have hs : horizon (child i) ≤ Finset.univ.sup (fun a ↦ horizon (child a)) :=
      Finset.le_sup (f := fun a ↦ horizon (child a)) (Finset.mem_univ i)
    change k ≤ 1 + Finset.univ.sup (fun a ↦ horizon (child a))
    omega
  | episode law returns regeneration child ih =>
    intro k hk
    obtain ⟨i, _, hchild⟩ := (PMF.mem_support_bind_iff law _ k).mp hk
    have hi := ih i k hchild
    have hs : horizon (child i) ≤ Finset.univ.sup (fun j ↦ horizon (child j)) :=
      Finset.le_sup (f := fun j ↦ horizon (child j)) (Finset.mem_univ i)
    change k ≤ 1 + Finset.univ.sup (fun j ↦ horizon (child j))
    omega

/-- Finite expectations of nonnegative real values agree with their nonnegative-integral
encoding. Every mass is finite because it belongs to a PMF. -/
theorem expectation_ofReal {n : ℕ} (law : PMF (Fin n)) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    expectation law (fun i ↦ ENNReal.ofReal (f i)) =
      ENNReal.ofReal (∑ i, (law i).toReal * f i) := by
  rw [expectation, tsum_fintype, ENNReal.ofReal_sum_of_nonneg
    (fun i _ ↦ mul_nonneg ENNReal.toReal_nonneg (hf i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (law.apply_ne_top i)]

/-- A Boolean split of a finite probability law needs only its total branch mass. -/
theorem weighted_if {n : ℕ} (law : PMF (Fin n)) (selected : Fin n → Bool) (u v : ℝ) :
    (∑ i, (law i).toReal * (if selected i then u else v)) =
      v + (u - v) * branchMass law selected := by
  have hterm (i : Fin n) : (law i).toReal * (if selected i then u else v) =
      v * (law i).toReal + (u - v) * (if selected i then (law i).toReal else 0) := by
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_real_mass]
  simp only [mul_one, branchMass]

/-- The potential is at least the terminal moment one whenever `q ≤ 1`. -/
theorem one_le_potential {q : ℝ} (hq : q ≤ 1) (phase : Phase) : 1 ≤ potential q phase := by
  cases phase <;> dsimp [potential] <;> linarith

/-- The exponential tilt used in the stopped-process bound. -/
noncomputable def theta (p q : ℝ) : ℝ := -Real.log (1 - p * q / 2)

/-- The tilt denominator is bounded away from zero under genuine hazard probabilities. -/
theorem tilt_denominator_pos {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hq0 : 0 ≤ q) :
    0 < 1 - p * q / 2 := by
  have hpq : p * q ≤ 1 := (mul_le_mul hp hq hq0 (by norm_num)).trans_eq (by norm_num)
  linarith

/-- Exact exponential value of the chosen tilt. -/
theorem exp_theta {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hq0 : 0 ≤ q) :
    Real.exp (theta p q) = (1 - p * q / 2)⁻¹ := by
  rw [theta, Real.exp_neg, Real.exp_log (tilt_denominator_pos hp hq hq0)]

/-- The free-phase Bellman identity closes at potential two. -/
theorem free_bellman_identity {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hq0 : 0 ≤ q) :
    Real.exp (theta p q) * (2 - p * q) = 2 := by
  rw [exp_theta hp hq hq0]
  have hd : 1 - p * q / 2 ≠ 0 := ne_of_gt (tilt_denominator_pos hp hq hq0)
  rw [show 2 - p * q = 2 * (1 - p * q / 2) by ring, mul_left_comm,
    inv_mul_cancel₀ hd, mul_one]

/-- The free attempt inequality uses only a current-history acceptance lower bound. -/
theorem free_bellman_le {p q a : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hq0 : 0 ≤ q)
    (ha : p ≤ a) : Real.exp (theta p q) * (2 - a * q) ≤ 2 := by
  calc
    Real.exp (theta p q) * (2 - a * q) ≤
        Real.exp (theta p q) * (2 - p * q) := by
      gcongr
    _ = 2 := free_bellman_identity hp hq hq0

/-- A held episode's regeneration bound closes at potential `2 - q`. -/
theorem held_bellman_le {q a : ℝ} (ha : a ≤ 1 - q) : 1 + a ≤ 2 - q := by linarith

/-- Monotonicity of nonnegative discrete expectations. -/
theorem expectation_mono {α : Type*} (law : PMF α) (f g : α → ℝ≥0∞)
    (hfg : ∀ a, f a ≤ g a) : expectation law f ≤ expectation law g :=
  ENNReal.tsum_le_tsum fun a ↦ mul_le_mul_right (hfg a) (law a)

/-- Constants integrate to themselves under a probability law. -/
theorem expectation_const {α : Type*} (law : PMF α) (c : ℝ≥0∞) :
    expectation law (fun _ ↦ c) = c := by
  simp only [expectation, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A common nonnegative scalar can be taken outside a discrete expectation. -/
theorem expectation_const_mul {α : Type*} (law : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expectation law (fun a ↦ c * f a) = c * expectation law f := by
  unfold expectation
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  ring

/-- Expected successor potential for one designated free proposal. -/
theorem weighted_attempt_potential {n : ℕ} (law : PMF (Fin n))
    (accepted : Fin n → Bool) (q : ℝ) :
    (∑ i, (law i).toReal * potential q (if accepted i then .held else .free)) =
      2 - branchMass law accepted * q := by
  calc
    _ = ∑ i, (law i).toReal * (if accepted i then 2 - q else 2) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      split_ifs <;> rfl
    _ = 2 + ((2 - q) - 2) * branchMass law accepted := weighted_if law accepted (2 - q) 2
    _ = _ := by ring

/-- Expected successor potential at the end of a held episode. -/
theorem weighted_episode_potential {n : ℕ} (law : PMF (Fin n))
    (returns : Fin n → Bool) (q : ℝ) :
    (∑ i, (law i).toReal * potential q (if returns i then .free else .absorbed)) =
      1 + branchMass law returns := by
  calc
    _ = ∑ i, (law i).toReal * (if returns i then 2 else 1) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      split_ifs <;> rfl
    _ = 1 + (2 - 1) * branchMass law returns := weighted_if law returns 2 1
    _ = _ := by ring

/-- Finite backward induction bounds the generating function at every node, even when every
node has its own history-dependent branch law and its own conditional regeneration outcomes. -/
theorem pgf_countLaw_le {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    pgf (ENNReal.ofReal (Real.exp (theta p q))) (countLaw tree) ≤
      ENNReal.ofReal (potential q phase) := by
  induction tree with
  | stop phase =>
    simpa only [countLaw, pgf, expectation_pure, pow_zero, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (one_le_potential hq phase)
  | idle law child ih =>
    change expectation (law.bind fun i ↦ countLaw (child i)) _ ≤ ENNReal.ofReal 2
    rw [expectation_bind]
    exact (expectation_mono law _ _ ih).trans_eq (expectation_const law _)
  | attempt law accepted hazard child ih =>
    change expectation (law.bind fun i ↦ (countLaw (child i)).map Nat.succ) _ ≤ ENNReal.ofReal 2
    rw [expectation_bind]
    change expectation law (fun i ↦ pgf _ ((countLaw (child i)).map Nat.succ)) ≤ _
    simp only [pgf_map_succ, expectation_const_mul]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (theta p q)) * expectation law
          (fun i ↦ ENNReal.ofReal (potential q (if accepted i then .held else .free))) :=
        mul_le_mul_right (expectation_mono law _ _ ih) _
      _ = ENNReal.ofReal (Real.exp (theta p q) *
          (2 - branchMass law accepted * q)) := by
        rw [expectation_ofReal law _ (fun i ↦ zero_le_one.trans (one_le_potential hq _)),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, weighted_attempt_potential]
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (free_bellman_le hp hq hq0 hazard)
  | episode law returns regeneration child ih =>
    change expectation (law.bind fun i ↦ countLaw (child i)) _ ≤ ENNReal.ofReal (2 - q)
    rw [expectation_bind]
    calc
      _ ≤ expectation law (fun i ↦
          ENNReal.ofReal (potential q (if returns i then .free else .absorbed))) :=
        expectation_mono law _ _ ih
      _ = ENNReal.ofReal (1 + branchMass law returns) := by
        rw [expectation_ofReal law _ (fun i ↦ zero_le_one.trans (one_le_potential hq _)),
          weighted_episode_potential]
      _ ≤ ENNReal.ofReal (2 - q) := ENNReal.ofReal_le_ofReal (held_bellman_le regeneration)

/-- The tilt has the explicit linear lower bound used in the tail estimate. -/
theorem theta_ge_half_mul {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hq0 : 0 ≤ q) :
    p * q / 2 ≤ theta p q := by
  have hlog := Real.log_le_sub_one_of_pos (tilt_denominator_pos hp hq hq0)
  dsimp only [theta]
  linarith

/-- Positive current acceptance and regeneration hazards give a positive tilt. -/
theorem theta_pos {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1) :
    0 < theta p q := by
  have hpq : 0 < p * q := mul_pos hp0 hq0
  have hd : 1 - p * q / 2 < 1 := by linarith
  exact neg_pos.mpr (Real.log_neg (tilt_denominator_pos hp hq hq0.le) hd)

/-- A generating function at an exponential base is the actual nonnegative exponential
moment under the tree's count law. -/
theorem pgf_exp_eq_lintegral (θ : ℝ) (law : PMF ℕ) :
    pgf (ENNReal.ofReal (Real.exp θ)) law =
      ∫⁻ k, ENNReal.ofReal (Real.exp (θ * (k : ℝ))) ∂law.toMeasure := by
  rw [pgf, expectation, lintegral_countable']
  apply tsum_congr
  intro k
  rw [law.toMeasure_apply_singleton k (measurableSet_singleton k), mul_comm θ,
    Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le, mul_comm]

/-- The finite-horizon stopped exponential moment is bounded by its free/held/absorbed
potential. In particular the initial phase may already be held. -/
theorem exponential_moment_le_potential {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    (∫⁻ k, ENNReal.ofReal (Real.exp (theta p q * (k : ℝ))) ∂(countLaw tree).toMeasure) ≤
      ENNReal.ofReal (potential q phase) := by
  rw [← pgf_exp_eq_lintegral]
  exact pgf_countLaw_le hp hq0 hq tree

/-- Every possible initial phase has stopped exponential moment at most two. -/
theorem exponential_moment_le_two {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    (∫⁻ k, ENNReal.ofReal (Real.exp (theta p q * (k : ℝ))) ∂(countLaw tree).toMeasure) ≤ 2 := by
  have hv : potential q phase ≤ 2 := by cases phase <;> dsimp [potential] <;> linarith
  exact (exponential_moment_le_potential hp hq0 hq tree).trans
    (by simpa using ENNReal.ofReal_le_ofReal hv)

/-- Exponential Markov gives a quantitative tail for the actual finite tree count law. -/
theorem count_tail_le {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) (threshold : ℝ) :
    (countLaw tree).toMeasure {k : ℕ | threshold ≤ (k : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-theta p q * threshold)) := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hne : ENNReal.ofReal (Real.exp (theta p q * threshold)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hm : Measurable (fun k : ℕ ↦ ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))) :=
    Measurable.of_discrete
  have hmark := meas_ge_le_lintegral_div (μ := (countLaw tree).toMeasure) hm.aemeasurable
    hne ENNReal.ofReal_ne_top
  have hsub : {k : ℕ | threshold ≤ (k : ℝ)} ⊆
      {k : ℕ | ENNReal.ofReal (Real.exp (theta p q * threshold)) ≤
        ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))} := by
    intro k hk
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hθ.le))
  calc
    _ ≤ (countLaw tree).toMeasure {k : ℕ |
        ENNReal.ofReal (Real.exp (theta p q * threshold)) ≤
          ENNReal.ofReal (Real.exp (theta p q * (k : ℝ)))} := measure_mono hsub
    _ ≤ _ := hmark
    _ ≤ 2 / ENNReal.ofReal (Real.exp (theta p q * threshold)) :=
      ENNReal.div_le_div_right (exponential_moment_le_two hp hq0.le hq tree) _
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      simp only [div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- The simpler hazard-product tail follows from `theta ≥ p*q/2` at nonnegative thresholds. -/
theorem count_tail_le_half_mul {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1) {phase : Phase} (tree : Tree p q phase)
    (threshold : ℝ) (ht : 0 ≤ threshold) :
    (countLaw tree).toMeasure {k : ℕ | threshold ≤ (k : ℝ)} ≤
      ENNReal.ofReal (2 * Real.exp (-(p * q / 2) * threshold)) := by
  apply (count_tail_le hp0 hp hq0 hq tree threshold).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact theta_ge_half_mul hp hq hq0.le

/-- The moment bound proves integrability of the actual real exponential, rather than
silently using the default value of an undefined real integral. -/
theorem integrable_exponential_count {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    Integrable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) (countLaw tree).toMeasure := by
  have hm : Measurable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) := Measurable.of_discrete
  apply (lintegral_ofReal_ne_top_iff_integrable
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k : ℕ ↦ (Real.exp_pos (theta p q * (k : ℝ))).le)).mp
  exact (lt_of_le_of_lt (exponential_moment_le_two hp hq0 hq tree) (by norm_num)).ne

/-- Real-valued expected exponential form of the stopped-process bound. -/
theorem integral_exponential_count_le_two {p q : ℝ} (hp : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    (∫ k : ℕ, Real.exp (theta p q * (k : ℝ)) ∂(countLaw tree).toMeasure) ≤ 2 := by
  have hm : Measurable (fun k : ℕ ↦ Real.exp (theta p q * (k : ℝ))) := Measurable.of_discrete
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun k : ℕ ↦ (Real.exp_pos (theta p q * (k : ℝ))).le)
    hm.aestronglyMeasurable]
  simpa using ENNReal.toReal_mono (by norm_num)
    (exponential_moment_le_two hp hq0 hq tree)

/-- The designated count is integrable when both hazards are positive. -/
theorem integrable_count {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1) (hq0 : 0 < q) (hq : q ≤ 1)
    {phase : Phase} (tree : Tree p q phase) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) (countLaw tree).toMeasure := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hexp := (integrable_exponential_count hp hq0.le hq tree).div_const (theta p q)
  apply hexp.mono' Measurable.of_discrete.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  apply (le_div_iff₀ hθ).mpr
  have hbound := Real.add_one_le_exp (theta p q * (k : ℝ))
  nlinarith

/-- The same finite-tree argument yields the geometric-scale mean without independence of
free-bout costs and regeneration outcomes. -/
theorem integral_count_le_inv_theta {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1) {phase : Phase} (tree : Tree p q phase) :
    (∫ k : ℕ, (k : ℝ) ∂(countLaw tree).toMeasure) ≤ (theta p q)⁻¹ := by
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hcount := integrable_count hp0 hp hq0 hq tree
  have hexp := integrable_exponential_count hp hq0.le hq tree
  have hlinear := (hcount.const_mul (theta p q)).add
    (integrable_const (μ := (countLaw tree).toMeasure) (1 : ℝ))
  have hbound := integral_mono hlinear hexp
    (fun k ↦ Real.add_one_le_exp (theta p q * (k : ℝ)))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hcount.const_mul (theta p q)) (integrable_const 1), integral_const_mul]
    at hbound
  have hmgf := integral_exponential_count_le_two hp hq0.le hq tree
  have hprod : (∫ k : ℕ, (k : ℝ) ∂(countLaw tree).toMeasure) * theta p q ≤ 1 := by
    simp only [integral_const, probReal_univ, one_smul] at hbound
    nlinarith
  simpa only [one_div] using (le_div_iff₀ hθ).mpr hprod

/-- Explicit mean bound in terms of the two conditional hazard constants. -/
theorem integral_count_le_two_div_mul {p q : ℝ} (hp0 : 0 < p) (hp : p ≤ 1)
    (hq0 : 0 < q) (hq : q ≤ 1) {phase : Phase} (tree : Tree p q phase) :
    (∫ k : ℕ, (k : ℝ) ∂(countLaw tree).toMeasure) ≤ 2 / (p * q) := by
  apply (integral_count_le_inv_theta hp0 hp hq0 hq tree).trans
  have hθ : 0 < theta p q := theta_pos hp0 hp hq0 hq
  have hpq : 0 < p * q := mul_pos hp0 hq0
  apply (le_div_iff₀ hpq).mpr
  have hbound : (p * q / 2) * (theta p q)⁻¹ ≤ 1 := by
    calc
      _ ≤ theta p q * (theta p q)⁻¹ :=
        mul_le_mul_of_nonneg_right (theta_ge_half_mul hp hq hq0.le) (inv_pos.mpr hθ).le
      _ = 1 := mul_inv_cancel₀ hθ.ne'
  nlinarith

end TieredMatching.StoppedHazards
