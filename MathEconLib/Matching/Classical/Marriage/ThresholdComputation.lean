/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Truncation
public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
public import MathEconLib.Matching.Classical.Marriage.OrderIdeals
public import MathEconLib.Matching.Classical.Marriage.LoneWolf

/-!
# Computing stable threshold generators by deferred acceptance

One woman-proposing DA run on a truncated market gives the least stable
realization of every feasible acceptable threshold.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v} [DecidableEq M] (mkt : MarriageMarket M W)

omit [DecidableEq M] in
private theorem exists_partner_of_threshold {μ : M ≃. W} {m : M} {threshold : W}
    (hacceptable : mkt.ltM m none (some threshold))
    (hthreshold : mkt.leM m (some threshold) (μ m)) : ∃ w, μ m = some w := by
  let := mkt.prefM m
  cases h : μ m with
  | none =>
    rw [h] at hthreshold
    exact ((not_le_of_gt hacceptable) hthreshold).elim
  | some w => exact ⟨w, rfl⟩

variable [Fintype M] [Fintype W] [DecidableEq W]

/-- A single executable woman-proposing DA run on the truncated market. -/
def thresholdDA (m : M) (threshold : W) : M ≃. W :=
  (mkt.truncateMan m threshold).womanGaleShapleyComputable

theorem thresholdDA_spec (m : M) (threshold : W)
    (hacceptable : mkt.ltM m none (some threshold))
    (hfeasible : ∃ μ : mkt.StableMatching,
      mkt.leM m (some threshold) (μ.matching m)) :
    mkt.IsStableMatching (mkt.thresholdDA m threshold) ∧
      mkt.leM m (some threshold) (mkt.thresholdDA m threshold m) := by
  let := mkt.prefM m
  obtain ⟨μ, hμthreshold⟩ := hfeasible
  obtain ⟨current, hcurrent⟩ := exists_partner_of_threshold mkt hacceptable hμthreshold
  have hμtruncated : (mkt.truncateMan m threshold).IsStableMatching μ.matching :=
    stable_truncateMan_of_stable mkt μ.isStable hcurrent (by simpa only [hcurrent] using hμthreshold)
  have hDA : (mkt.truncateMan m threshold).IsStableMatching
      (mkt.thresholdDA m threshold) :=
    (mkt.truncateMan m threshold).stable_womanGaleShapleyComputable
  have hnotnone : mkt.thresholdDA m threshold m ≠ none := by
    intro hnone
    have hμnone := ((mkt.truncateMan m threshold).eq_none_iff_of_stable hDA hμtruncated m).mp hnone
    rw [hcurrent] at hμnone
    cases hμnone
  cases h : mkt.thresholdDA m threshold m with
  | none => exact (hnotnone h).elim
  | some w =>
    refine ⟨stable_of_stable_truncateMan mkt (le_of_lt hacceptable) hDA h, ?_⟩
    have hir := hDA.1.1 m
    change (mkt.truncateMan m threshold).leM m none (mkt.thresholdDA m threshold m) at hir
    rw [h] at hir
    exact (truncateMan_none_le_some mkt m threshold w).mp hir

theorem thresholdDA_le {m : M} {threshold : W}
    (hacceptable : mkt.ltM m none (some threshold))
    (ν : mkt.StableMatching) (hν : mkt.leM m (some threshold) (ν.matching m)) (m' : M) :
    mkt.leM m' (mkt.thresholdDA m threshold m') (ν.matching m') := by
  let := mkt.prefM m
  obtain ⟨current, hcurrent⟩ := exists_partner_of_threshold mkt hacceptable hν
  have hνtruncated := stable_truncateMan_of_stable mkt ν.isStable hcurrent
    (by simpa only [hcurrent] using hν)
  have hle := (mkt.truncateMan m threshold).womanGaleShapleyComputable_manPessimal hνtruncated m'
  by_cases hm : m' = m
  · subst m'
    have hspec := thresholdDA_spec mkt m threshold hacceptable ⟨ν, hν⟩
    obtain ⟨w, hw⟩ := exists_partner_of_threshold mkt hacceptable hspec.2
    change (mkt.truncateMan m threshold).leM m (mkt.thresholdDA m threshold m) (ν.matching m) at hle
    rw [hw, hcurrent] at hle ⊢
    exact (truncateMan_leM_some_some mkt m m threshold w current).mp hle
  · exact (truncateMan_leM_of_ne mkt m m' threshold hm _ _).mp hle

/-- The executable matching, packaged with its proved original-market stability. -/
def thresholdDAStable (m : M) (threshold : W)
    (hacceptable : mkt.ltM m none (some threshold))
    (hfeasible : ∃ μ : mkt.StableMatching,
      mkt.leM m (some threshold) (μ.matching m)) : mkt.StableMatching where
  matching := mkt.thresholdDA m threshold
  isStable := (thresholdDA_spec mkt m threshold hacceptable hfeasible).1

/-- A feasible intrinsic threshold generator is computed by one DA run. -/
theorem thresholdDAStable_eq_generator (m : M) (threshold : W)
    (hacceptable : mkt.ltM m none (some threshold))
    (hfeasible : ∃ μ : mkt.StableMatching,
      mkt.leM m (some threshold) (μ.matching m)) :
    thresholdDAStable mkt m threshold hacceptable hfeasible =
      StableMatching.thresholdGenerator mkt m (some threshold) := by
  apply le_antisymm
  · apply (StableMatching.le_iff_menWeaklyPrefer mkt).mpr
    intro m'
    exact thresholdDA_le mkt hacceptable _
      (StableMatching.thresholdGenerator_meets mkt hfeasible) m'
  · exact StableMatching.thresholdGenerator_le mkt
      (thresholdDA_spec mkt m threshold hacceptable hfeasible).2

theorem thresholdDA_eq_generator_matching (m : M) (threshold : W)
    (hacceptable : mkt.ltM m none (some threshold))
    (hfeasible : ∃ μ : mkt.StableMatching,
      mkt.leM m (some threshold) (μ.matching m)) :
    mkt.thresholdDA m threshold =
      (StableMatching.thresholdGenerator mkt m (some threshold)).matching := by
  exact congrArg StableMatching.matching
    (thresholdDAStable_eq_generator mkt m threshold hacceptable hfeasible)

/-- Compute a stable threshold candidate, rejecting unacceptable and infeasible
thresholds by comparisons and the outcome of a single finite DA run. -/
def thresholdCandidate (m : M) (threshold : W) : Option mkt.StableMatching := by
  let := mkt.prefM m
  exact if hacceptable : none < some threshold then
    let μ := mkt.thresholdDA m threshold
    if hnone : μ m = none then none else
      some ⟨μ, by
        have hDA : (mkt.truncateMan m threshold).IsStableMatching μ :=
          (mkt.truncateMan m threshold).stable_womanGaleShapleyComputable
        cases h : μ m with
        | none => exact (hnone h).elim
        | some w => exact stable_of_stable_truncateMan mkt hacceptable.le hDA h⟩
  else none

theorem thresholdCandidate_eq_some (m : M) (threshold : W)
    (hacceptable : mkt.ltM m none (some threshold))
    (hfeasible : ∃ μ : mkt.StableMatching,
      mkt.leM m (some threshold) (μ.matching m)) :
    mkt.thresholdCandidate m threshold =
      some (thresholdDAStable mkt m threshold hacceptable hfeasible) := by
  let := mkt.prefM m
  have hacc : (none : Option W) < some threshold := hacceptable
  obtain ⟨w, hw⟩ := exists_partner_of_threshold mkt hacceptable
    (thresholdDA_spec mkt m threshold hacceptable hfeasible).2
  have hnone : mkt.thresholdDA m threshold m ≠ none := by
    rw [hw]
    exact Option.some_ne_none _
  simp only [thresholdCandidate, dite_eq_left hacc, dite_eq_right hnone]
  rfl

theorem thresholdCandidate_eq_of_generator (m : M) (threshold : W)
    (ν : mkt.StableMatching) (hacceptable : mkt.ltM m none (some threshold))
    (hν : mkt.leM m (some threshold) (ν.matching m))
    (hgenerator : StableMatching.thresholdGenerator mkt m (some threshold) = ν) :
    mkt.thresholdCandidate m threshold = some ν := by
  rw [thresholdCandidate_eq_some mkt m threshold hacceptable ⟨ν, hν⟩,
    thresholdDAStable_eq_generator, hgenerator]

theorem thresholdCandidate_some_spec {m : M} {threshold : W} {μ : mkt.StableMatching}
    (hresult : mkt.thresholdCandidate m threshold = some μ) :
    mkt.ltM m none (some threshold) ∧
      StableMatching.MeetsThreshold mkt m (some threshold) μ ∧
      StableMatching.thresholdGenerator mkt m (some threshold) = μ := by
  let := mkt.prefM m
  unfold thresholdCandidate at hresult
  dsimp only at hresult
  split at hresult
  · rename_i hacceptable
    split at hresult
    · cases hresult
    · rename_i hnone
      cases hresult
      have hDA : (mkt.truncateMan m threshold).IsStableMatching (mkt.thresholdDA m threshold) :=
        (mkt.truncateMan m threshold).stable_womanGaleShapleyComputable
      have hstable : mkt.IsStableMatching (mkt.thresholdDA m threshold) := by
        cases h : mkt.thresholdDA m threshold m with
        | none => exact (hnone h).elim
        | some w => exact stable_of_stable_truncateMan mkt hacceptable.le hDA h
      have hthreshold : mkt.leM m (some threshold) (mkt.thresholdDA m threshold m) := by
        cases h : mkt.thresholdDA m threshold m with
        | none => exact (hnone h).elim
        | some w =>
          apply (truncateMan_none_le_some mkt m threshold w).mp
          have hir : (mkt.truncateMan m threshold).leM m none (mkt.thresholdDA m threshold m) :=
            hDA.1.1 m
          rw [h] at hir
          exact hir
      refine ⟨hacceptable, hthreshold, ?_⟩
      exact (thresholdDAStable_eq_generator mkt m threshold hacceptable
        ⟨⟨mkt.thresholdDA m threshold, hstable⟩, hthreshold⟩).symm
  · cases hresult

omit [DecidableEq M] [DecidableEq W] in
/-- Every feasible coordinate generator except bottom is join-prime. -/
theorem thresholdGenerator_supPrime {m : M} {o : Option W}
    (hfeasible : ∃ μ : mkt.StableMatching, StableMatching.MeetsThreshold mkt m o μ)
    (hne : StableMatching.thresholdGenerator mkt m o ≠ ⊥) :
    SupPrime (StableMatching.thresholdGenerator mkt m o) := by
  let := mkt.prefM m
  refine ⟨?_, ?_⟩
  · simpa only [isMin_iff_eq_bot] using hne
  · intro μ ν hle
    have hgen := StableMatching.thresholdGenerator_meets mkt hfeasible
    have hcoord := (StableMatching.le_iff_menWeaklyPrefer mkt).mp hle m
    have hthreshold : o ≤ (μ ⊔ ν).matching m := hgen.trans hcoord
    rw [StableMatching.matching_sup_apply] at hthreshold
    change o ≤ max (μ.matching m) (ν.matching m) at hthreshold
    rcases le_max_iff.mp hthreshold with hμ | hν
    · exact Or.inl (StableMatching.thresholdGenerator_le mkt hμ)
    · exact Or.inr (StableMatching.thresholdGenerator_le mkt hν)

/-- A finite candidate list obtained by running the explicit threshold routine
once on each supplied man/partner pair. No stable matching enumeration is used. -/
def thresholdCandidates (men : List M) (women : List W) : List mkt.StableMatching :=
  (men.product women).filterMap (fun p => mkt.thresholdCandidate p.1 p.2)

theorem thresholdCandidates_length (men : List M) (women : List W) :
    (mkt.thresholdCandidates men women).length ≤ men.length * women.length := by
  calc
    (mkt.thresholdCandidates men women).length ≤ (men.product women).length :=
      List.length_filterMap_le _ _
    _ = men.length * women.length := List.length_product men women

end MathEconLib.Matching.MarriageMarket
