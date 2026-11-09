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

public import TieredMatching.ConcreteLaw
public import TieredMatching.ReferenceModel
public import TieredMatching.Labels

/-!
# The terminal holder is the winner of the actual source-prefix race

For the concrete arrival allocation, the actual per-tier proposer counts specify the exact
original-label source prefixes used by each woman. On injective source rows, her terminal
holder comes from the unique minimum of their union. This identity is deterministic.
-/

@[expose] public section

namespace TieredMatching.ArrivalWinner

open StableMarriage Arrival
open scoped NNReal

/-- The source union indexed by actual proposal counts is exactly the used source row. -/
theorem mem_actual_sourceSet_iff_used {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m)))
    (w s : Fin n) :
    let p := profile P (adaptiveAllocation (pick P manTier) x (n * n))
    s ∈ ReferenceModel.sourceSet manTier (fun j ↦ proposalCount manTier j p w) ↔
      (w, s) ∈ usedSources P manTier (allocationHistory (pick P manTier) x (n * n)) := by
  classical
  dsimp only
  simp only [ReferenceModel.sourceSet, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hs⟩
    rw [← usedMen_terminal_eq_prefix P manTier x hx w j] at hs
    exact (Finset.mem_filter.mp hs).2
  · intro hs
    refine ⟨manTier s, ?_⟩
    rw [← usedMen_terminal_eq_prefix P manTier x hx w (manTier s)]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hs⟩

/-- A terminal held man is allocated from the unique minimum of the actual source prefixes. -/
theorem terminal_source_winner {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m)))
    (w m : Fin n)
    (hheld : (deferredAcceptance
      (profile P (adaptiveAllocation (pick P manTier) x (n * n)))).held w = some m) :
    let h := allocationHistory (pick P manTier) x (n * n)
    let p := profile P (adaptiveAllocation (pick P manTier) x (n * n))
    ReferenceRace.winner
      (ReferenceModel.sourceSet manTier (fun j ↦ proposalCount manTier j p w))
      (fun s ↦ x (w, s)) = some (((replay P manTier h).2 (w, m)).2) := by
  classical
  let h := allocationHistory (pick P manTier) x (n * n)
  let π := (replay P manTier h).2
  let y := adaptiveAllocation (pick P manTier) x (n * n)
  let p := profile P y
  let S := ReferenceModel.sourceSet manTier (fun j ↦ proposalCount manTier j p w)
  change (deferredAcceptance p).held w = some m at hheld
  change ReferenceRace.winner S (fun s ↦ x (w, s)) = some ((π (w, m)).2)
  have hπ : PreservesBlocks manTier π := replay_preservesBlocks P manTier h
  have hrow (k : Fin n) : π (w, k) = (w, (π (w, k)).2) :=
    Prod.ext (congrArg (fun b : Fin n × Fin J ↦ b.1) (hπ (w, k))) rfl
  have hyEq : y = x ∘ π := by
    simp only [y, adaptiveAllocation, ← replay_reindex]
    rfl
  have hy : ∀ w, Function.Injective (fun k ↦ y (w, k)) := by
    rw [hyEq]
    exact row_injective_reindex manTier π hπ x hx
  have hstate : (replay P manTier h).1.state = deferredAcceptance p :=
    allocation_terminal_state P manTier x hx
  have hquery (k : Fin n) : Queried P (replay P manTier h).1 (w, k) ↔
      HasProposed p (deferredAcceptance p) k w := by
    unfold Queried HasProposed
    rw [hstate]
    rfl
  have hbest := terminal_held_isMinOn p w m hheld
  have hused := (history_used_queried P manTier x (n * n) (w, m)).mpr
    ((hquery m).mpr hbest.1)
  change π (w, m) ∈ usedSources P manTier h at hused
  rw [hrow m] at hused
  apply (ReferenceRace.winner_eq_some_iff_strict S (fun s ↦ x (w, s)) (hx w).injOn _).mpr
  refine ⟨(mem_actual_sourceSet_iff_used P manTier x hx w _).mpr hused, ?_⟩
  intro k hk hne
  have husedk := (mem_actual_sourceSet_iff_used P manTier x hx w k).mp hk
  let o := (π.symm (w, k)).2
  have hpre : π.symm (w, k) = (w, o) := by
    have hb := hπ (π.symm (w, k))
    simp only [Equiv.apply_symm_apply, block] at hb
    exact Prod.ext (congrArg Prod.fst hb).symm rfl
  have hforward : π (w, o) = (w, k) := by
    rw [← hpre, Equiv.apply_symm_apply]
  have hqk := (history_used_queried P manTier x (n * n) (π.symm (w, k))).mp (by
    change π (π.symm (w, k)) ∈ usedSources P manTier h
    simpa only [Equiv.apply_symm_apply] using husedk)
  have hprop : HasProposed p (deferredAcceptance p) o w := by
    apply (hquery o).mp
    simpa only [hpre] using hqk
  have hrank := hbest.2 hprop
  have hscore : y (w, m) ≤ y (w, o) := by
    apply le_of_not_gt
    intro hgt
    have hr := (exponentialRank_lt_iff (fun k ↦ y (w, k)) (hy w) o m).mpr hgt
    exact (not_lt_of_ge hrank) hr
  rw [hyEq] at hscore
  change x (π (w, m)) ≤ x (π (w, o)) at hscore
  rw [hrow m, hforward] at hscore
  exact lt_of_le_of_ne hscore (fun heq ↦ hne ((hx w heq).symm))

/-- The exact terminal held tier is the source race category at the actual proposal counts. -/
theorem heldTier_eq_tierCategory {n J : ℕ} [NeZero n]
    (P : Fin n → Equiv.Perm (Fin n)) (manTier : Fin n → Fin J)
    (x : Edge n → ℝ) (hx : ∀ w, Function.Injective (fun m ↦ x (w, m)))
    (w : Fin n) :
    let p := profile P (adaptiveAllocation (pick P manTier) x (n * n))
    heldTier manTier p w = ReferenceModel.tierCategory manTier
      (fun j ↦ proposalCount manTier j p w) (fun s ↦ x (w, s)) := by
  classical
  let p := profile P (adaptiveAllocation (pick P manTier) x (n * n))
  obtain ⟨μ, hμ⟩ := terminal_complete_matching p
  have hwinner := terminal_source_winner P manTier x hx w (μ.symm w) (hμ w)
  change ((deferredAcceptance p).held w).map manTier =
    (ReferenceRace.winner
      (ReferenceModel.sourceSet manTier (fun j ↦ proposalCount manTier j p w))
      (fun s ↦ x (w, s))).map manTier
  rw [hμ w, hwinner]
  simp only [Option.map_some]
  apply congrArg some
  exact (congrArg (fun b : Fin n × Fin J ↦ b.2)
    (replay_preservesBlocks P manTier
      (allocationHistory (pick P manTier) x (n * n)) (w, μ.symm w))).symm

/-- The deterministic winner identity holds almost surely under the exact arrival input law. -/
theorem ae_arrival_heldTier_eq_tierCategory {n J : ℕ} [NeZero n]
    (P : Fin n → Fin n → ℝ≥0) (manTier : Fin n → Fin J)
    (β : Fin J → ℝ≥0) (hβ : ∀ j, 0 < β j) :
    ∀ᵐ z ∂arrivalInputLaw P (fun m _ ↦ β (manTier m)), ∀ w,
      let p := arrivalProfile (fun r ↦ pick r manTier) (n * n) z
      heldTier manTier p w = ReferenceModel.tierCategory manTier
        (fun j ↦ proposalCount manTier j p w) (fun s ↦ z.2 (w, s)) := by
  filter_upwards [ae_injective_input_women P (fun m _ ↦ β (manTier m))
    (fun m _ ↦ hβ (manTier m))] with z hz w
  exact heldTier_eq_tierCategory (arrivalMenRanks z.1) manTier z.2 hz w

end TieredMatching.ArrivalWinner
