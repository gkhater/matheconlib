/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.ComputedChains
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Executable ordered man rows of the computed irreducible poset. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v} [Fintype M] [Fintype W]
variable [DecidableEq M] [DecidableEq W] (mkt : MarriageMarket M W)

def rowLe (men : List M) (women : List W) (m : M)
    (i j : Fin (mkt.computedIrreducibles men women).length) : Prop :=
  mkt.leM m (some (mkt.generatingPair men women i).2)
    (some (mkt.generatingPair men women j).2)

@[instance_reducible]
def rowLeDecidable (men : List M) (women : List W) (m : M) :
    DecidableRel (mkt.rowLe men women m) :=
  fun i j => (mkt.prefM m).toDecidableLE
    (some (mkt.generatingPair men women i).2) (some (mkt.generatingPair men women j).2)

/-- Restrict to a man's chosen generators and sort in his threshold order. -/
def sortedRow (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M) :
    List (Fin (mkt.computedIrreducibles men women).length) :=
  letI := mkt.rowLeDecidable men women m
  (remaining.filter (fun i => decide ((mkt.generatingPair men women i).1 = m))).mergeSort
    (fun i j => decide (mkt.rowLe men women m i j))

theorem sortedRow_perm (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M) :
    (mkt.sortedRow men women remaining m).Perm
      (remaining.filter (fun i => decide ((mkt.generatingPair men women i).1 = m))) := by
  exact List.mergeSort_perm _ _

@[simp] theorem mem_sortedRow (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M)
    (i : Fin (mkt.computedIrreducibles men women).length) :
    i ∈ mkt.sortedRow men women remaining m ↔
      i ∈ remaining ∧ (mkt.generatingPair men women i).1 = m := by
  simpa only [List.mem_filter, decide_eq_true_eq] using
    (sortedRow_perm mkt men women remaining m).mem_iff

theorem sortedRow_length (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M) :
    (mkt.sortedRow men women remaining m).length =
      (remaining.filter (fun i => decide ((mkt.generatingPair men women i).1 = m))).length :=
  (sortedRow_perm mkt men women remaining m).length_eq

theorem sortedRow_nodup (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M)
    (hnodup : remaining.Nodup) : (mkt.sortedRow men women remaining m).Nodup :=
  (sortedRow_perm mkt men women remaining m).nodup_iff.mpr (hnodup.filter _)

theorem sortedRow_pairwise_rowLe (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M) :
    (mkt.sortedRow men women remaining m).Pairwise (mkt.rowLe men women m) := by
  let := mkt.prefM m
  let := mkt.rowLeDecidable men women m
  let : Std.Total (mkt.rowLe men women m) := ⟨fun i j => le_total _ _⟩
  let : IsTrans (Fin (mkt.computedIrreducibles men women).length) (mkt.rowLe men women m) :=
    ⟨fun _ _ _ hij hjk => le_trans hij hjk⟩
  exact List.pairwise_mergeSort' _ _

theorem sortedRow_pairwise (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) (m : M) :
    (mkt.sortedRow men women remaining m).Pairwise
      (fun i j => (mkt.computedIrreducibles men women).get i ≤
        (mkt.computedIrreducibles men women).get j) := by
  apply (sortedRow_pairwise_rowLe mkt men women remaining m).imp_of_mem
  intro i j hi hj hle
  have him := ((mem_sortedRow mkt men women remaining m i).mp hi).2
  have hjm := ((mem_sortedRow mkt men women remaining m j).mp hj).2
  apply generating_le_of_preference mkt men women i j (him.trans hjm.symm)
  rw [him]
  exact hle

/-- The row partition contains each residual point exactly once. -/
theorem sum_sortedRow_lengths (men : List M) (women : List W)
    (remaining : List (Fin (mkt.computedIrreducibles men women).length)) :
    (∑ m : M, (mkt.sortedRow men women remaining m).length) = remaining.length := by
  simp_rw [sortedRow_length]
  induction remaining with
  | nil => simp
  | cons i remaining ih =>
      simp only [List.filter_cons]
      simp only [List.length_cons]
      simp_rw [show ∀ m : M,
        (if decide ((mkt.generatingPair men women i).1 = m) then
          i :: remaining.filter (fun j => decide ((mkt.generatingPair men women j).1 = m))
        else remaining.filter (fun j => decide ((mkt.generatingPair men women j).1 = m))).length =
          (if (mkt.generatingPair men women i).1 = m then 1 else 0) +
            (remaining.filter (fun j => decide ((mkt.generatingPair men women j).1 = m))).length by
        intro m; split <;> simp_all [Nat.add_comm]]
      simp [Finset.sum_add_distrib, ih, Nat.add_comm]

end MathEconLib.Matching.MarriageMarket
