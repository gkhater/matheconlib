/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.ComputedRows
public import MathEconLib.ForMathlib.Data.List.BoundedChunks
public import Mathlib.Algebra.BigOperators.Fin

/-! Explicit short chain blocks of a residual computed irreducible poset. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

variable {m n : Nat} (mkt : MarriageMarket (Fin m) (Fin n))

def sortedRows
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :=
  (List.finRange m).flatMap (fun r =>
    mkt.sortedRow (List.finRange m) (List.finRange n) remaining r)

theorem mem_sortedRows
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length))
    (i : Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length) :
    i ∈ mkt.sortedRows remaining ↔ i ∈ remaining := by
  constructor
  · intro hi
    obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hi
    exact ((mem_sortedRow mkt _ _ remaining r i).mp hr).1
  · intro hi
    apply List.mem_flatMap.mpr
    refine ⟨(mkt.generatingPair _ _ i).1, List.mem_finRange _, ?_⟩
    exact (mem_sortedRow mkt _ _ remaining _ i).mpr ⟨hi, rfl⟩

theorem sortedRows_nodup
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length))
    (hnodup : remaining.Nodup) : (mkt.sortedRows remaining).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro r _
    exact sortedRow_nodup mkt _ _ remaining r hnodup
  · apply (List.nodup_finRange m).imp
    intro r s hrs
    apply List.disjoint_left.mpr
    intro i hir his
    have hr := ((mem_sortedRow mkt _ _ remaining r i).mp hir).2
    have hs := ((mem_sortedRow mkt _ _ remaining s i).mp his).2
    exact hrs (hr.symm.trans hs)

theorem sortedRows_perm
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length))
    (hnodup : remaining.Nodup) : (mkt.sortedRows remaining).Perm remaining := by
  apply (List.perm_ext_iff_of_nodup (sortedRows_nodup mkt remaining hnodup) hnodup).mpr
  exact mem_sortedRows mkt remaining

/-- The chain blocks actually constructed at one residual leaf. -/
def rowBlocks (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :=
  (List.finRange m).flatMap (fun r =>
    ListChunks.chunks D (mkt.sortedRow (List.finRange m) (List.finRange n) remaining r))

private theorem flatten_flatMap {α β : Type*} (input : List α) (f : α → List (List β)) :
    (input.flatMap f).flatten = input.flatMap (fun x => (f x).flatten) := by
  induction input with
  | nil => rfl
  | cons x input ih => simp [ih]

theorem flatten_rowBlocks (D : Nat) (hD : 0 < D)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    (mkt.rowBlocks D remaining).flatten = mkt.sortedRows remaining := by
  unfold rowBlocks
  rw [flatten_flatMap]
  simp only [ListChunks.flatten_chunks D hD]
  rfl

theorem rowBlocks_perm (D : Nat) (hD : 0 < D)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length))
    (hnodup : remaining.Nodup) : (mkt.rowBlocks D remaining).flatten.Perm remaining := by
  rw [flatten_rowBlocks mkt D hD]
  exact sortedRows_perm mkt remaining hnodup

theorem rowBlocks_nonempty (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    ∀ block ∈ mkt.rowBlocks D remaining, block ≠ [] := by
  intro block hblock
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hblock
  exact ListChunks.nonempty_of_mem hr

theorem rowBlocks_length_le (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    ∀ block ∈ mkt.rowBlocks D remaining, block.length ≤ D := by
  intro block hblock
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hblock
  exact ListChunks.length_le_of_mem hr

theorem rowBlocks_pairwise (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    ∀ block ∈ mkt.rowBlocks D remaining,
      block.Pairwise (fun i j =>
        (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).get i ≤
        (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).get j) := by
  intro block hblock
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hblock
  exact (sortedRow_pairwise mkt _ _ remaining r).sublist (ListChunks.sublist_of_mem hr)

theorem rowBlocks_length (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    (mkt.rowBlocks D remaining).length =
      ∑ r : Fin m, (ListChunks.chunks D
        (mkt.sortedRow (List.finRange m) (List.finRange n) remaining r)).length := by
  unfold rowBlocks
  rw [List.length_flatMap, ← List.ofFn_eq_map]
  exact Fin.sum_ofFn _

theorem rowBlocks_count_mul_le (D : Nat)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length)) :
    (mkt.rowBlocks D remaining).length * D ≤ remaining.length + m * D := by
  rw [rowBlocks_length, Finset.sum_mul]
  calc
    (∑ r : Fin m, (ListChunks.chunks D
        (mkt.sortedRow (List.finRange m) (List.finRange n) remaining r)).length * D) ≤
        ∑ r : Fin m, ((mkt.sortedRow (List.finRange m) (List.finRange n) remaining r).length + D) := by
      apply Finset.sum_le_sum
      intro r _
      exact ListChunks.count_mul_le _ _
    _ = remaining.length + m * D := by
      rw [Finset.sum_add_distrib, sum_sortedRow_lengths]
      simp

theorem rowBlocks_count_le_twice (D : Nat) (hD : 0 < D)
    (remaining : List (Fin (mkt.computedIrreducibles (List.finRange m) (List.finRange n)).length))
    (hsmall : remaining.length ≤ m * D) : (mkt.rowBlocks D remaining).length ≤ 2 * m := by
  have hcount := rowBlocks_count_mul_le mkt D remaining
  have hbound : (mkt.rowBlocks D remaining).length * D ≤ (2 * m) * D := by nlinarith
  by_contra h
  have hlarge := mul_lt_mul_of_pos_right (Nat.lt_of_not_ge h) hD
  omega

end MathEconLib.Matching.MarriageMarket
