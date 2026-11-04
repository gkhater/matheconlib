/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.ComputedPoset
public import Mathlib.Data.List.Find

/-!
# Computable chain labels for generated irreducibles

Search the finite candidate-pair list for a witness generating each computed
irreducible. Equal-man fibres are chains. This gives an executable chain
assignment for compact leaf encodings; classical choices used in the separate
thin-chain centrality proof are not consulted by this construction.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v} [Fintype M] [Fintype W]
variable [DecidableEq M] [DecidableEq W] (mkt : MarriageMarket M W)

def pairMatches (men : List M) (women : List W)
    (i : Fin (mkt.computedIrreducibles men women).length) (p : M × W) : Bool :=
  letI := mkt.stableMatchingDecidableEq
  decide (mkt.thresholdCandidate p.1 p.2 =
    some ((mkt.computedIrreducibles men women).get i))

theorem exists_generating_pair (men : List M) (women : List W)
    (i : Fin (mkt.computedIrreducibles men women).length) :
    ∃ p ∈ men.product women, mkt.pairMatches men women i p = true := by
  have hmem := List.get_mem (mkt.computedIrreducibles men women) i
  have hcand := ((mem_computedIrreducibles mkt men women _).mp hmem).1
  obtain ⟨p, hp, hresult⟩ := List.mem_filterMap.mp hcand
  refine ⟨p, hp, ?_⟩
  simpa only [pairMatches, decide_eq_true_eq] using hresult

theorem generatingPair_isSome (men : List M) (women : List W)
    (i : Fin (mkt.computedIrreducibles men women).length) :
    ((men.product women).find? (mkt.pairMatches men women i)).isSome := by
  obtain ⟨p, hp, hmatches⟩ := exists_generating_pair mkt men women i
  cases hf : (men.product women).find? (mkt.pairMatches men women i) with
  | none =>
      exact ((List.find?_eq_none.mp hf) p hp hmatches).elim
  | some p => simp

/-- A deterministic witness obtained by a finite search over participant pairs. -/
def generatingPair (men : List M) (women : List W)
    (i : Fin (mkt.computedIrreducibles men women).length) : M × W :=
  ((men.product women).find? (mkt.pairMatches men women i)).get
    (generatingPair_isSome mkt men women i)

theorem generatingPair_spec (men : List M) (women : List W)
    (i : Fin (mkt.computedIrreducibles men women).length) :
    mkt.thresholdCandidate (mkt.generatingPair men women i).1
      (mkt.generatingPair men women i).2 =
      some ((mkt.computedIrreducibles men women).get i) := by
  have hf : (men.product women).find? (mkt.pairMatches men women i) =
      some (mkt.generatingPair men women i) :=
    (Option.coe_get (generatingPair_isSome mkt men women i)).symm
  have h := List.find?_some hf
  simpa only [pairMatches, decide_eq_true_eq] using h

theorem generatingPair_injective (men : List M) (women : List W) :
    Function.Injective (mkt.generatingPair men women) := by
  intro i j h
  apply (computedIrreducibles_nodup mkt men women).injective_get
  apply Option.some.inj
  calc
    some ((mkt.computedIrreducibles men women).get i) =
        mkt.thresholdCandidate (mkt.generatingPair men women i).1
          (mkt.generatingPair men women i).2 := (generatingPair_spec mkt men women i).symm
    _ = mkt.thresholdCandidate (mkt.generatingPair men women j).1
          (mkt.generatingPair men women j).2 := by rw [h]
    _ = some ((mkt.computedIrreducibles men women).get j) := generatingPair_spec mkt men women j

theorem generating_le_of_preference (men : List M) (women : List W)
    (i j : Fin (mkt.computedIrreducibles men women).length)
    (hman : (mkt.generatingPair men women i).1 = (mkt.generatingPair men women j).1)
    (hpref : mkt.leM (mkt.generatingPair men women i).1
      (some (mkt.generatingPair men women i).2) (some (mkt.generatingPair men women j).2)) :
    (mkt.computedIrreducibles men women).get i ≤ (mkt.computedIrreducibles men women).get j := by
  have hi := thresholdCandidate_some_spec mkt (generatingPair_spec mkt men women i)
  have hj := thresholdCandidate_some_spec mkt (generatingPair_spec mkt men women j)
  rw [← hi.2.2]
  apply StableMatching.thresholdGenerator_le mkt
  have hmeet : mkt.leM (mkt.generatingPair men women j).1
      (some (mkt.generatingPair men women j).2)
      (((mkt.computedIrreducibles men women).get j).matching
        (mkt.generatingPair men women j).1) := hj.2.1
  rw [← hman] at hmeet
  let := mkt.prefM (mkt.generatingPair men women i).1
  exact hpref.trans hmeet

theorem same_generating_man_comparable (men : List M) (women : List W)
    (i j : Fin (mkt.computedIrreducibles men women).length)
    (hman : (mkt.generatingPair men women i).1 = (mkt.generatingPair men women j).1) :
    (mkt.computedIrreducibles men women).get i ≤ (mkt.computedIrreducibles men women).get j ∨
      (mkt.computedIrreducibles men women).get j ≤ (mkt.computedIrreducibles men women).get i := by
  let := mkt.prefM (mkt.generatingPair men women i).1
  rcases le_total (some (mkt.generatingPair men women i).2)
      (some (mkt.generatingPair men women j).2) with h | h
  · exact Or.inl (generating_le_of_preference mkt men women i j hman h)
  · right
    apply generating_le_of_preference mkt men women j i hman.symm
    rw [← hman]
    exact h

end MathEconLib.Matching.MarriageMarket
