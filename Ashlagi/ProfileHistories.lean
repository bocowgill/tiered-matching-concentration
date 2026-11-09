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

public import Ashlagi.ProtocolKernel
public import Ashlagi.StoppedProcess
public import Ashlagi.VisitBounds

/-! # Literal actual protocol histories and finite conditional towers

A child history is the actual next observable entry prepended to the revealed newest-first
history. Its event is exactly its parent's event intersected with that next observation fiber.
Conditional tower identities follow under the same original finite preference-profile law.
-/

@[expose] public section

namespace Ashlagi.ProfileHistories

open StableMarriage MeasureTheory Ashlagi.Ordinal FiniteConditioning
open scoped ENNReal

/-- The actual revealed profile transcript event. -/
def event {n : ℕ} (C : Protocols.Protocol n) (h : List (Entry n)) : Set (Profile n) :=
  {p | Protocols.profileTranscript C p h.length = h}

/-- The next observation reads the same original profile after only the fixed revealed history. -/
noncomputable def nextObservation {n : ℕ} (C : Protocols.Protocol n)
    (h : List (Entry n)) (p : Profile n) : Entry n :=
  Protocols.observation C p.manRank (profilePriorities p) h

/-- Original profile law conditioned on precisely the observed finite history. -/
noncomputable def lawAt {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) : PMF (Profile n) := condition μ (event C h)

/-- The next-entry law is the pushforward of that same past-conditioned original profile. -/
noncomputable def nextLaw {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) : PMF (Entry n) := (lawAt μ C h).map (nextObservation C h)

/-- Exact literal one-step prefix refinement, including malformed or impossible histories. -/
theorem event_cons {n : ℕ} (C : Protocols.Protocol n) (h : List (Entry n))
    (entry : Entry n) : event C (entry :: h) = event C h ∩ {p | nextObservation C h p = entry} := by
  ext p
  exact Protocols.profileTranscript_cons_iff C p h entry

/-- A nonnull observed next entry has a nonnull original child-prefix event. -/
theorem child_nonnull {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (entry : Entry n) (hh : eventMass μ (event C h) ≠ 0)
    (he : nextLaw μ C h entry ≠ 0) : eventMass μ (event C (entry :: h)) ≠ 0 := by
  rw [event_cons, ← eventMass_mul_conditional_event, eventMass_observation_fiber]
  exact mul_ne_zero hh he

/-- On every nonnull next-entry branch, iterated conditioning is exactly the child history law. -/
theorem condition_next {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (entry : Entry n) (hh : eventMass μ (event C h) ≠ 0)
    (he : nextLaw μ C h entry ≠ 0) :
    condition (lawAt μ C h) {p | nextObservation C h p = entry} = lawAt μ C (entry :: h) := by
  rw [lawAt, lawAt, event_cons]
  exact StoppedProcess.condition_inter μ _ _ (by
    rw [← event_cons]
    exact child_nonnull μ C h entry hh he)

/-- Disintegrating by the actual next observable entry and using literal child history laws
recovers the current conditional profile law. Null branches carry zero bind weight. -/
theorem bind_next_lawAt {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) :
    (nextLaw μ C h).bind (fun entry ↦ lawAt μ C (entry :: h)) = lawAt μ C h := by
  calc
    _ = (nextLaw μ C h).bind
        (fun entry ↦ condition (lawAt μ C h) {p | nextObservation C h p = entry}) := by
      apply StoppedProcess.bind_congr_support
      intro entry he
      exact (condition_next μ C h entry hh he).symm
    _ = lawAt μ C h := bind_condition_eq _ _

/-- The full pushforward tower holds for every observable function of the original profile. -/
theorem map_next_lawAt {n : ℕ} {β : Type*} (μ : PMF (Profile n))
    (C : Protocols.Protocol n) (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0)
    (f : Profile n → β) :
    (lawAt μ C h).map f =
      (nextLaw μ C h).bind (fun entry ↦ (lawAt μ C (entry :: h)).map f) := by
  rw [← bind_next_lawAt μ C h hh, PMF.map_bind]

/-- A child-prefix-supported profile has exactly its parent's observed next entry. -/
theorem child_support_next {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (entry : Entry n) (hh : eventMass μ (event C h) ≠ 0)
    (he : nextLaw μ C h entry ≠ 0) (p : Profile n) (hp : lawAt μ C (entry :: h) p ≠ 0) :
    nextObservation C h p = entry := by
  have hs : p ∈ (condition μ (event C (entry :: h))).support := hp
  rw [support_condition μ _ (child_nonnull μ C h entry hh he), event_cons] at hs
  exact hs.1.2

/-- The tower may use branch-specific observables that agree on each positive child support. -/
theorem map_next_lawAt_congr {n : ℕ} {β : Type*} (μ : PMF (Profile n))
    (C : Protocols.Protocol n) (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0)
    (f : Profile n → β) (g : Entry n → Profile n → β)
    (hg : ∀ entry, nextLaw μ C h entry ≠ 0 → ∀ p,
      lawAt μ C (entry :: h) p ≠ 0 → f p = g entry p) :
    (lawAt μ C h).map f =
      (nextLaw μ C h).bind (fun entry ↦ (lawAt μ C (entry :: h)).map (g entry)) := by
  rw [map_next_lawAt μ C h hh]
  apply StoppedProcess.bind_congr_support
  intro entry he
  exact StoppedProcess.Process.map_congr_support _ _ _ (hg entry he)

/-- A finite PMF bind has the literal sum of products of real point masses. -/
theorem toReal_bind_apply {R Ω : Type*} [Fintype R] (ν : PMF R) (K : R → PMF Ω) (ω : Ω) :
    ((ν.bind K) ω).toReal = ∑ r, (ν r).toReal * (K r ω).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun r _ ↦ ENNReal.mul_ne_top (ν.apply_ne_top r) ((K r).apply_ne_top ω))]
  simp only [ENNReal.toReal_mul]

/-- Real finite expectations disintegrate exactly over a finite PMF bind. -/
theorem expectation_bind {R Ω : Type*} [Fintype R] [Fintype Ω]
    (ν : PMF R) (K : R → PMF Ω) (f : Ω → ℝ) :
    VisitBounds.expectation (ν.bind K) f =
      ∑ r, (ν r).toReal * VisitBounds.expectation (K r) f := by
  simp only [VisitBounds.expectation, toReal_bind_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

/-- The real finite-expectation tower for literal actual protocol child-prefix laws. -/
theorem expectation_next_lawAt {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) (f : Profile n → ℝ) :
    VisitBounds.expectation (lawAt μ C h) f =
      ∑ entry, (nextLaw μ C h entry).toReal *
        VisitBounds.expectation (lawAt μ C (entry :: h)) f := by
  rw [← bind_next_lawAt μ C h hh, expectation_bind]

/-- Branch-dependent real observables may be substituted when they agree on positive child
supports. This is the finite conditional tower used by chronological reward recursions. -/
theorem expectation_next_lawAt_congr {n : ℕ} (μ : PMF (Profile n))
    (C : Protocols.Protocol n) (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0)
    (f : Profile n → ℝ) (g : Entry n → Profile n → ℝ)
    (hg : ∀ entry, nextLaw μ C h entry ≠ 0 → ∀ p,
      lawAt μ C (entry :: h) p ≠ 0 → f p = g entry p) :
    VisitBounds.expectation (lawAt μ C h) f =
      ∑ entry, (nextLaw μ C h entry).toReal *
        VisitBounds.expectation (lawAt μ C (entry :: h)) (g entry) := by
  rw [expectation_next_lawAt μ C h hh]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases he : nextLaw μ C h entry = 0
  · simp only [he, ENNReal.toReal_zero, zero_mul]
  · congr 1
    unfold VisitBounds.expectation
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : lawAt μ C (entry :: h) p = 0
    · simp only [hp, ENNReal.toReal_zero, zero_mul]
    · rw [hg entry he p hp]

/-- The same exact finite-history tower in measure-integral form. All real functions on the
finite profile space are integrable, so no additional regularity hypothesis is required. -/
theorem integral_next_lawAt {n : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h : List (Entry n)) (hh : eventMass μ (event C h) ≠ 0) (f : Profile n → ℝ) :
    (∫ p, f p ∂(lawAt μ C h).toMeasure) =
      ∑ entry, (nextLaw μ C h entry).toReal *
        (∫ p, f p ∂(lawAt μ C (entry :: h)).toMeasure) := by
  simpa only [VisitBounds.expectation_eq_integral] using expectation_next_lawAt μ C h hh f

/-- Canonical histories up to clock H contain exactly one entry per elapsed step. -/
abbrev Hist (n H : ℕ) := Σ t : Fin (H + 1), Fin t.val → Entry n

namespace Hist

/-- The literal observation clock encoded by a bounded finite history. -/
def clock {n H : ℕ} (h : Hist n H) : ℕ := h.1.val

/-- Decode the newest-first finite entry tuple. -/
def decode {n H : ℕ} (h : Hist n H) : List (Entry n) := List.ofFn h.2

/-- The observation clock is bounded by the chosen deterministic horizon. -/
theorem clock_le {n H : ℕ} (h : Hist n H) : clock h ≤ H := by
  have hh := h.1.isLt
  change h.1.val ≤ H
  omega

/-- Decoding has exactly the recorded clock length. -/
theorem length_decode {n H : ℕ} (h : Hist n H) : (decode h).length = clock h := by
  simp only [decode, List.length_ofFn, clock]

/-- A bounded observed list has its exact canonical finite encoding. -/
def encode {n H : ℕ} (L : List (Entry n)) (hL : L.length ≤ H) : Hist n H :=
  ⟨⟨L.length, by omega⟩, L.get⟩

/-- Encoding preserves the observation clock exactly. -/
theorem clock_encode {n H : ℕ} (L : List (Entry n)) (hL : L.length ≤ H) :
    clock (encode L hL) = L.length := rfl

/-- Decoding an actual list encoding returns the literal original list. -/
theorem decode_encode {n H : ℕ} (L : List (Entry n)) (hL : L.length ≤ H) :
    decode (encode L hL) = L := List.ofFn_get L

/-- Distinct bounded history labels cannot encode the same finite prefix. -/
theorem decode_injective {n H : ℕ} : Function.Injective (decode : Hist n H → List (Entry n)) := by
  rintro ⟨t, u⟩ ⟨s, v⟩ h
  have hts : t = s := Fin.ext (by
    have hh := congrArg List.length h
    simpa only [decode, List.length_ofFn] using hh)
  subst s
  change List.ofFn u = List.ofFn v at h
  have huv : u = v := List.ofFn_injective h
  subst v
  rfl

/-- Every bounded history is exactly the encoding of its decoded list. -/
theorem encode_decode {n H : ℕ} (h : Hist n H) :
    encode (decode h) (by rw [length_decode]; exact clock_le h) = h := by
  apply decode_injective
  exact decode_encode _ _

/-- Standard finite labels for consumers requiring `Fin M` observation states. -/
noncomputable def indexEquiv (n H : ℕ) : Hist n H ≃ Fin (Fintype.card (Hist n H)) :=
  Fintype.equivFin _

/-- The actual profile prefix event represented by a bounded finite history label. -/
def prefixEvent {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) : Set (Profile n) :=
  event C (decode h)

/-- Membership uses the exact recorded clock, not a padded longer alias. -/
theorem mem_prefixEvent_iff {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) (p : Profile n) :
    p ∈ prefixEvent C h ↔ Protocols.profileTranscript C p (clock h) = decode h := by
  simp only [prefixEvent, event, Set.mem_ofPred_eq, length_decode]

/-- One actual next observation is prepended to this literal prefix; at the horizon the label
is unchanged. The map observes the same original profile and samples no new random input. -/
noncomputable def step {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) (p : Profile n) :
    Hist n H :=
  if ht : clock h < H then
    encode (nextObservation C (decode h) p :: decode h) (by
      simp only [List.length_cons, length_decode]
      omega)
  else h

/-- Before the horizon, every actual next observation advances the clock by exactly one. -/
theorem clock_step {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) (p : Profile n)
    (ht : clock h < H) : clock (step C h p) = clock h + 1 := by
  simp only [step, dite_eq_left ht, clock_encode, List.length_cons, length_decode]

/-- Before the horizon, the child is the actual new entry followed by the exact parent list. -/
theorem decode_step {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) (p : Profile n)
    (ht : clock h < H) :
    decode (step C h p) = nextObservation C (decode h) p :: decode h := by
  simp only [step, dite_eq_left ht, decode_encode]

/-- Equality of single-step child labels is exactly equality of the observed next entry. -/
theorem step_eq_iff_observation {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H)
    (p q : Profile n) (ht : clock h < H) :
    step C h p = step C h q ↔ nextObservation C (decode h) p = nextObservation C (decode h) q := by
  constructor
  · intro he
    have hh := congrArg decode he
    rw [decode_step C h p ht, decode_step C h q ht] at hh
    exact (List.cons.inj hh).1
  · intro he
    apply decode_injective
    rw [decode_step C h p ht, decode_step C h q ht, he]

/-- A realized child prefix is literally its parent prefix intersected with the next-label
fiber. This identity is proved for every profile, without a supplied tree-refinement premise. -/
theorem prefixEvent_step {n H : ℕ} (C : Protocols.Protocol n) (h : Hist n H) (q : Profile n) :
    prefixEvent C (step C h q) = prefixEvent C h ∩ {p | step C h p = step C h q} := by
  classical
  by_cases ht : clock h < H
  · have he : prefixEvent C (step C h q) =
        event C (nextObservation C (decode h) q :: decode h) := by
      rw [prefixEvent, decode_step C h q ht]
    rw [he, event_cons]
    change event C (decode h) ∩ {p | nextObservation C (decode h) p =
        nextObservation C (decode h) q} =
      event C (decode h) ∩ {p | step C h p = step C h q}
    congr 1
    ext p
    exact (step_eq_iff_observation C h p q ht).symm
  · simp only [step, dite_eq_right ht, Set.ofPred_true, Set.inter_univ]

/-- Positive conditional child branches satisfy exactly the refinement required by finite
stopped/competing processes. Parent nonnullness is not needed for this stronger label identity. -/
theorem step_refines {n H : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h j : Hist n H)
    (hj : ((condition μ (prefixEvent C h)).map (step C h)) j ≠ 0) :
    prefixEvent C j = prefixEvent C h ∩ {p | step C h p = j} := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (step C h)
    (condition μ (prefixEvent C h)) j).mp hj
  subst j
  exact prefixEvent_step C h p

/-- Every positive pre-horizon child branch makes strict chronological progress. -/
theorem step_progress {n H : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (h j : Hist n H) (ht : clock h < H)
    (hj : ((condition μ (prefixEvent C h)).map (step C h)) j ≠ 0) : clock h < clock j := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (step C h)
    (condition μ (prefixEvent C h)) j).mp hj
  subst j
  rw [clock_step C h p ht]
  omega

/-- The uninformative root has no recorded observation. -/
def root (n H : ℕ) : Hist n H := encode [] (Nat.zero_le H)

/-- The actual empty-prefix event is the full original profile space. -/
theorem prefixEvent_root {n H : ℕ} (C : Protocols.Protocol n) :
    prefixEvent C (root n H) = Set.univ := by
  ext p
  simp only [prefixEvent, root, decode_encode, event, List.length_nil,
    Protocols.profileTranscript, Protocols.transcript, Set.mem_ofPred_eq, Set.mem_univ]

/-- Clock on the standard finite index labels required by finite observation processes. -/
noncomputable def indexedClock (n H : ℕ) (i : Fin (Fintype.card (Hist n H))) : ℕ :=
  clock ((indexEquiv n H).symm i)

/-- Actual original-profile prefix event on standard finite index labels. -/
noncomputable def indexedEvent {n H : ℕ} (C : Protocols.Protocol n)
    (i : Fin (Fintype.card (Hist n H))) : Set (Profile n) :=
  prefixEvent C ((indexEquiv n H).symm i)

/-- Actual next prefix observation on standard finite index labels. -/
noncomputable def indexedStep {n H : ℕ} (C : Protocols.Protocol n)
    (i : Fin (Fintype.card (Hist n H))) (p : Profile n) : Fin (Fintype.card (Hist n H)) :=
  indexEquiv n H (step C ((indexEquiv n H).symm i) p)

/-- Every indexed visible clock is at most the literal observation horizon. -/
theorem indexedClock_le {n H : ℕ} (i : Fin (Fintype.card (Hist n H))) :
    indexedClock n H i ≤ H := clock_le _

/-- The exact positive-branch prefix refinement in the standard finite-index interface. -/
theorem indexedStep_refines {n H : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (i j : Fin (Fintype.card (Hist n H)))
    (hj : ((condition μ (indexedEvent C i)).map (indexedStep C i)) j ≠ 0) :
    indexedEvent C j = indexedEvent C i ∩ {p | indexedStep C i p = j} := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (indexedStep C i)
    (condition μ (indexedEvent C i)) j).mp hj
  have hchild : (indexEquiv n H).symm j = step C ((indexEquiv n H).symm i) p := by
    rw [← he]
    exact (indexEquiv n H).symm_apply_apply _
  change prefixEvent C ((indexEquiv n H).symm j) =
    prefixEvent C ((indexEquiv n H).symm i) ∩
      {q | indexEquiv n H (step C ((indexEquiv n H).symm i) q) = j}
  rw [hchild, prefixEvent_step]
  congr 1
  ext q
  rw [← hchild]
  exact Equiv.eq_symm_apply (indexEquiv n H)

/-- Standard indexed child labels make strict progress before the observation horizon. -/
theorem indexedStep_progress {n H : ℕ} (μ : PMF (Profile n)) (C : Protocols.Protocol n)
    (i j : Fin (Fintype.card (Hist n H))) (ht : indexedClock n H i < H)
    (hj : ((condition μ (indexedEvent C i)).map (indexedStep C i)) j ≠ 0) :
    indexedClock n H i < indexedClock n H j := by
  obtain ⟨p, hp, he⟩ := (PMF.mem_support_map_iff (indexedStep C i)
    (condition μ (indexedEvent C i)) j).mp hj
  have hchild : (indexEquiv n H).symm j = step C ((indexEquiv n H).symm i) p := by
    rw [← he]
    exact (indexEquiv n H).symm_apply_apply _
  change clock ((indexEquiv n H).symm i) < clock ((indexEquiv n H).symm j)
  rw [hchild, clock_step C _ p ht]
  omega

/-- The indexed empty-prefix root is uninformative under the original profile law. -/
theorem indexedEvent_root {n H : ℕ} (C : Protocols.Protocol n) :
    indexedEvent C (indexEquiv n H (root n H)) = Set.univ := by
  simp only [indexedEvent, Equiv.symm_apply_apply, prefixEvent_root]

end Hist

end Ashlagi.ProfileHistories
