/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.IrreducibleComputation

/-!
# An explicitly indexed, computed irreducible poset

Its elements are positions in the computed duplicate-free candidate list.
Comparisons use the supplied preference orders on men's assignments. The
order isomorphism with intrinsic irreducibles is a proved correctness result;
neither the construction nor its comparisons enumerate stable matchings.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v} [Fintype M] [Fintype W]
variable [DecidableEq M] [DecidableEq W] (mkt : MarriageMarket M W)

/-- The order is decided through the actual finite preference comparisons. -/
@[instance_reducible]
def computedIrreducibleOrder (men : List M) (women : List W) :
    PartialOrder (Fin (mkt.computedIrreducibles men women).length) where
  le i j := ∀ m : M, mkt.leM m
    (((mkt.computedIrreducibles men women).get i).matching m)
    (((mkt.computedIrreducibles men women).get j).matching m)
  lt i j := (∀ m : M, mkt.leM m
      (((mkt.computedIrreducibles men women).get i).matching m)
      (((mkt.computedIrreducibles men women).get j).matching m)) ∧
    ¬ ∀ m : M, mkt.leM m
      (((mkt.computedIrreducibles men women).get j).matching m)
      (((mkt.computedIrreducibles men women).get i).matching m)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl i m := by
    let := mkt.prefM m
    exact le_rfl
  le_trans i j k hij hjk m := by
    let := mkt.prefM m
    exact (hij m).trans (hjk m)
  le_antisymm i j hij hji := by
    apply (computedIrreducibles_nodup mkt men women).injective_get
    apply StableMatching.ext mkt
    apply PEquiv.ext
    intro m
    let := mkt.prefM m
    exact le_antisymm (hij m) (hji m)

/-- Computable order decisions, without a `Fintype` of all stable matchings. -/
@[instance_reducible]
def computedIrreducibleDecidableLE (men : List M) (women : List W) :
    @DecidableLE (Fin (mkt.computedIrreducibles men women).length)
      (mkt.computedIrreducibleOrder men women).toLE := by
  intro i j
  change Decidable (∀ m : M, mkt.leM m
    (((mkt.computedIrreducibles men women).get i).matching m)
    (((mkt.computedIrreducibles men women).get j).matching m))
  letI : DecidablePred (fun m : M => mkt.leM m
      (((mkt.computedIrreducibles men women).get i).matching m)
      (((mkt.computedIrreducibles men women).get j).matching m)) :=
    fun m => (mkt.prefM m).toDecidableLE _ _
  infer_instance

/-- Positions enumerate exactly the intrinsic join-irreducibles. -/
def computedIrreducibleEquiv (men : List M) (women : List W)
    (hmen : ∀ m : M, m ∈ men) (hwomen : ∀ w : W, w ∈ women) :
    Fin (mkt.computedIrreducibles men women).length ≃
      {μ : mkt.StableMatching // SupIrred μ} := by
  letI := mkt.stableMatchingDecidableEq
  exact
    { toFun := fun i => ⟨(mkt.computedIrreducibles men women).get i,
        supIrred_of_mem_computedIrreducibles mkt men women _ (List.get_mem _ _)⟩
      invFun := fun j => ⟨(mkt.computedIrreducibles men women).idxOf j.1,
        List.idxOf_lt_length_of_mem
          (mem_computedIrreducibles_of_supIrred mkt men women hmen hwomen j.1 j.2)⟩
      left_inv := fun i => by
        apply Fin.ext
        exact List.get_idxOf (computedIrreducibles_nodup mkt men women) i
      right_inv := fun j => by
        apply Subtype.ext
        exact List.getElem_idxOf _ }

/-- The explicit comparison relation agrees with the intrinsic lattice order. -/
def computedIrreducibleOrderIso (men : List M) (women : List W)
    (hmen : ∀ m : M, m ∈ men) (hwomen : ∀ w : W, w ∈ women) :
    @OrderIso (Fin (mkt.computedIrreducibles men women).length)
      {μ : mkt.StableMatching // SupIrred μ}
      (mkt.computedIrreducibleOrder men women).toLE inferInstance := by
  letI : LE (Fin (mkt.computedIrreducibles men women).length) :=
    (mkt.computedIrreducibleOrder men women).toLE
  exact
    { toEquiv := mkt.computedIrreducibleEquiv men women hmen hwomen
      map_rel_iff' := by
        intro i j
        change (mkt.computedIrreducibles men women).get i ≤
          (mkt.computedIrreducibles men women).get j ↔
          ∀ m : M, mkt.leM m
            (((mkt.computedIrreducibles men women).get i).matching m)
            (((mkt.computedIrreducibles men women).get j).matching m)
        exact StableMatching.le_iff_menWeaklyPrefer mkt }

end MathEconLib.Matching.MarriageMarket
