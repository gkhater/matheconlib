/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.ThresholdComputation
public import MathEconLib.Matching.Classical.Marriage.IrreducibleChains
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.ProdSigma

/-!
# Computing all intrinsic stable-matching irreducibles

There is one finite DA candidate per supplied man/partner pair. Remove bottom
and repeated candidates. The resulting list contains exactly the intrinsic
join-irreducibles when the participant lists are exhaustive. The definitions
do not enumerate the type of all stable matchings.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v} [Fintype M] [Fintype W]
variable [DecidableEq M] [DecidableEq W] (mkt : MarriageMarket M W)

/-- Equality is decided by the explicitly finite list of men's assignments. -/
@[instance_reducible]
def stableMatchingDecidableEq : DecidableEq mkt.StableMatching := by
  intro μ ν
  apply decidable_of_iff (∀ m : M, μ.matching m = ν.matching m)
  constructor
  · intro h
    apply StableMatching.ext mkt
    apply PEquiv.ext
    exact h
  · intro h m
    exact congrArg (fun σ : mkt.StableMatching => σ.matching m) h

/-- Compute the bottom stable matching by the existing executable DA. -/
def computedBottom : mkt.StableMatching where
  matching := mkt.womanGaleShapleyComputable
  isStable := mkt.stable_womanGaleShapleyComputable

theorem computedBottom_eq_bot : mkt.computedBottom = ⊥ := by
  apply StableMatching.ext mkt
  exact mkt.womanGaleShapleyComputable_eq_womanOptimalMatching.trans
    (StableMatching.matching_bot mkt).symm

/-- A computed list, using only pairwise DA runs and finite comparisons. -/
def computedIrreducibles (men : List M) (women : List W) : List mkt.StableMatching :=
  letI := mkt.stableMatchingDecidableEq
  ((mkt.thresholdCandidates men women).filter (fun μ => decide (μ ≠ mkt.computedBottom))).dedup

theorem mem_computedIrreducibles (men : List M) (women : List W) (μ : mkt.StableMatching) :
    μ ∈ mkt.computedIrreducibles men women ↔
      μ ∈ mkt.thresholdCandidates men women ∧ μ ≠ ⊥ := by
  simp [computedIrreducibles, computedBottom_eq_bot]

theorem computedIrreducibles_nodup (men : List M) (women : List W) :
    (mkt.computedIrreducibles men women).Nodup := by
  let := mkt.stableMatchingDecidableEq
  unfold computedIrreducibles
  exact List.nodup_dedup _

theorem computedIrreducibles_length (men : List M) (women : List W) :
    (mkt.computedIrreducibles men women).length ≤ men.length * women.length := by
  let := mkt.stableMatchingDecidableEq
  change (((mkt.thresholdCandidates men women).filter
    (fun μ => decide (μ ≠ mkt.computedBottom))).dedup).length ≤ men.length * women.length
  calc
    (((mkt.thresholdCandidates men women).filter
        (fun μ => decide (μ ≠ mkt.computedBottom))).dedup).length ≤
        ((mkt.thresholdCandidates men women).filter (fun μ => decide (μ ≠ mkt.computedBottom))).length :=
      (List.dedup_sublist _).length_le
    _ ≤ (mkt.thresholdCandidates men women).length := List.length_filter_le _ _
    _ ≤ men.length * women.length := thresholdCandidates_length mkt men women

theorem supIrred_of_mem_computedIrreducibles (men : List M) (women : List W)
    (μ : mkt.StableMatching) (hμ : μ ∈ mkt.computedIrreducibles men women) : SupIrred μ := by
  obtain ⟨hμ, hne⟩ := (mem_computedIrreducibles mkt men women μ).mp hμ
  obtain ⟨⟨m, w⟩, _, hresult⟩ := List.mem_filterMap.mp hμ
  have hspec := thresholdCandidate_some_spec mkt hresult
  have hprime := thresholdGenerator_supPrime mkt ⟨μ, hspec.2.1⟩
    (by rw [hspec.2.2]; exact hne)
  rw [hspec.2.2] at hprime
  exact hprime.supIrred

theorem mem_computedIrreducibles_of_supIrred (men : List M) (women : List W)
    (hmen : ∀ m : M, m ∈ men) (hwomen : ∀ w : W, w ∈ women)
    (μ : mkt.StableMatching) (hμ : SupIrred μ) :
    μ ∈ mkt.computedIrreducibles men women := by
  let j : {ν : mkt.StableMatching // SupIrred ν} := ⟨μ, hμ⟩
  let m := (StableMatching.irreducibleLabel mkt j).1
  let w := (StableMatching.irreducibleLabel mkt j).2
  have hmatching : μ.matching m = some w := StableMatching.irreducibleLabel_matching mkt j
  have hacceptable : mkt.ltM m none (some w) := by
    let := mkt.prefM m
    have hir : mkt.leM m none (μ.matching m) := μ.isStable.1.1 m
    rw [hmatching] at hir
    exact lt_of_le_of_ne hir (by simp)
  have hthreshold : mkt.leM m (some w) (μ.matching m) := by
    let := mkt.prefM m
    rw [hmatching]
    exact le_rfl
  have hresult : mkt.thresholdCandidate m w = some μ :=
    thresholdCandidate_eq_of_generator mkt m w μ hacceptable hthreshold
      (StableMatching.irreducibleLabel_generator mkt j)
  apply (mem_computedIrreducibles mkt men women μ).mpr
  refine ⟨?_, hμ.ne_bot⟩
  apply List.mem_filterMap.mpr
  exact ⟨(m, w), List.mem_product.mpr ⟨hmen m, hwomen w⟩, hresult⟩

theorem mem_computedIrreducibles_iff (men : List M) (women : List W)
    (hmen : ∀ m : M, m ∈ men) (hwomen : ∀ w : W, w ∈ women) (μ : mkt.StableMatching) :
    μ ∈ mkt.computedIrreducibles men women ↔ SupIrred μ :=
  ⟨supIrred_of_mem_computedIrreducibles mkt men women μ,
    mem_computedIrreducibles_of_supIrred mkt men women hmen hwomen μ⟩

end MathEconLib.Matching.MarriageMarket
