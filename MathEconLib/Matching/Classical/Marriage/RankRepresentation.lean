/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.RankSymmetry
public import Mathlib.Data.Finset.Sort

/-! Every finite balanced marriage market has an explicit rank-list presentation. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

def optionAt {n : Nat} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val, h⟩ else none

private theorem optionAt_optionIndex {n : Nat} (o : Option (Fin n)) :
    optionAt (optionIndex o) = o := by
  cases o with
  | none => simp [optionAt, optionIndex]
  | some i => simp [optionAt, optionIndex, i.isLt]

private theorem optionAt_injective {n : Nat} : Function.Injective (@optionAt n) := by
  intro i j h
  have hi : optionIndex (optionAt i) = i := by
    unfold optionAt
    split_ifs with hlt
    · apply Fin.ext; rfl
    · apply Fin.ext; simp only [optionIndex]; omega
  have hj : optionIndex (optionAt j) = j := by
    unfold optionAt
    split_ifs with hlt
    · apply Fin.ext; rfl
    · apply Fin.ext; simp only [optionIndex]; omega
  calc i = optionIndex (optionAt i) := hi.symm
    _ = optionIndex (optionAt j) := congrArg optionIndex h
    _ = j := hj

noncomputable def orderRank {n : Nat}
    (order : LinearOrder (Option (Fin n))) (o : Option (Fin n)) : Fin (n + 1) := by
  letI : LinearOrder (Option (Fin n)) := order
  letI : LE (Option (Fin n)) := order.toLE
  letI : LT (Option (Fin n)) := order.toLT
  exact (Fintype.orderIsoFinOfCardEq (Option (Fin n)) (by simp)).symm o

private theorem orderRank_injective {n : Nat}
    (order : LinearOrder (Option (Fin n))) :
    Function.Injective (orderRank order) := by
  intro a b h
  letI : LinearOrder (Option (Fin n)) := order
  letI : LE (Option (Fin n)) := order.toLE
  letI : LT (Option (Fin n)) := order.toLT
  exact (Fintype.orderIsoFinOfCardEq (Option (Fin n)) (by simp)).symm.injective h

private theorem orderRank_le_iff {n : Nat}
    (order : LinearOrder (Option (Fin n))) (a b : Option (Fin n)) :
    (orderRank order a).val ≤ (orderRank order b).val ↔
      @LE.le (Option (Fin n)) order.toLE a b := by
  letI : LinearOrder (Option (Fin n)) := order
  letI : LE (Option (Fin n)) := order.toLE
  letI : LT (Option (Fin n)) := order.toLT
  change (orderRank order a ≤ orderRank order b) ↔
    @LE.le (Option (Fin n)) order.toLE a b
  exact (Fintype.orderIsoFinOfCardEq (Option (Fin n)) (by simp)).symm.le_iff_le

/-- A row with one distinct rank per optional partner, in the original order. -/
noncomputable def rowOfOrder {n : Nat}
    (order : LinearOrder (Option (Fin n))) : List Nat :=
  (List.finRange (n + 1)).map (fun i => (orderRank order (optionAt i)).val)

theorem rowOfOrder_length {n : Nat} (order : LinearOrder (Option (Fin n))) :
    (rowOfOrder order).length = n + 1 := by
  simp [rowOfOrder]

theorem rowOfOrder_nodup {n : Nat} (order : LinearOrder (Option (Fin n))) :
    (rowOfOrder order).Nodup := by
  unfold rowOfOrder
  apply List.Nodup.map _ (List.nodup_finRange (n + 1))
  intro i j h
  apply optionAt_injective
  apply orderRank_injective order
  exact Fin.ext h

theorem rowOfOrder_bound {n : Nat} (order : LinearOrder (Option (Fin n)))
    {r : Nat} (hr : r ∈ rowOfOrder order) : r ≤ n := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact Nat.lt_succ_iff.mp (orderRank order (optionAt i)).isLt

private theorem rowOfOrder_get {n : Nat}
    (order : LinearOrder (Option (Fin n))) (o : Option (Fin n)) :
    (rowOfOrder order).getD (optionIndex o).val 0 =
      (orderRank order o).val := by
  have hi : (optionIndex o).val < (rowOfOrder order).length := by
    rw [rowOfOrder_length]
    exact (optionIndex o).isLt
  rw [List.getD_eq_getElem _ _ hi]
  unfold rowOfOrder at *
  simp only [List.getElem_map, List.getElem_finRange]
  cases o with
  | none => simp [optionAt, optionIndex, Fin.cast]
  | some i => simp [optionAt, optionIndex, Fin.cast, i.isLt]

/-- Construct rank rows from the market's actual finite linear orders. -/
noncomputable def rankRepresentation {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) : RankInput where
  men := (List.finRange n).map (fun m => rowOfOrder (mkt.prefM m))
  women := (List.finRange n).map (fun w => rowOfOrder (mkt.prefW w))
  women_length := by simp
  men_row_length := by
    intro row hr
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hr
    simpa using rowOfOrder_length (mkt.prefM m)
  women_row_length := by
    intro row hr
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hr
    simpa using rowOfOrder_length (mkt.prefW w)
  men_row_nodup := by
    intro row hr
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hr
    exact rowOfOrder_nodup _
  women_row_nodup := by
    intro row hr
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hr
    exact rowOfOrder_nodup _

theorem rankRepresentation_length {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    (rankRepresentation mkt).men.length = n := by
  simp [rankRepresentation]

theorem rankRepresentation_bound {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    (∀ row ∈ (rankRepresentation mkt).men, ∀ r ∈ row, r ≤ n) ∧
    (∀ row ∈ (rankRepresentation mkt).women, ∀ r ∈ row, r ≤ n) := by
  constructor
  · intro row hr r hrr
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hr
    exact rowOfOrder_bound _ hrr
  · intro row hr r hrr
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hr
    exact rowOfOrder_bound _ hrr

private theorem rankAt_rankRepresentation_men {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) (m : Fin n)
    (o : Option (Fin n)) :
    rankAt (rankRepresentation mkt).men m.val (optionIndex o).val =
      (orderRank (mkt.prefM m) o).val := by
  unfold rankAt rankRepresentation
  have hi : m.val < ((List.finRange n).map
      (fun m => rowOfOrder (mkt.prefM m))).length := by
    simp
  rw [List.getD_eq_getElem _ _ hi]
  simp only [List.getElem_map, List.getElem_finRange]
  exact rowOfOrder_get _ _

private theorem rankAt_rankRepresentation_women {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) (w : Fin n)
    (o : Option (Fin n)) :
    rankAt (rankRepresentation mkt).women w.val (optionIndex o).val =
      (orderRank (mkt.prefW w) o).val := by
  unfold rankAt rankRepresentation
  have hi : w.val < ((List.finRange n).map
      (fun w => rowOfOrder (mkt.prefW w))).length := by
    simp
  rw [List.getD_eq_getElem _ _ hi]
  simp only [List.getElem_map, List.getElem_finRange]
  exact rowOfOrder_get _ _

/-- The representation denotes exactly the original market. -/
theorem rankRepresentation_market {n : Nat}
    (mkt : MarriageMarket (Fin n) (Fin n)) :
    castFin (rankRepresentation_length mkt) (rankRepresentation mkt).market = mkt := by
  apply eq_of_pref_le
  · intro m a b
    change (castFin (rankRepresentation_length mkt)
      (rankRepresentation mkt).market).leM m a b ↔ mkt.leM m a b
    rw [castFin_leM, (rankRepresentation mkt).leM_iff]
    simp only [optionIndex_map_cast_val]
    simp only [Fin.cast]
    rw [rankAt_rankRepresentation_men, rankAt_rankRepresentation_men]
    exact orderRank_le_iff (mkt.prefM m) a b
  · intro w a b
    change (castFin (rankRepresentation_length mkt)
      (rankRepresentation mkt).market).leW w a b ↔ mkt.leW w a b
    rw [castFin_leW, (rankRepresentation mkt).leW_iff]
    simp only [optionIndex_map_cast_val]
    simp only [Fin.cast]
    rw [rankAt_rankRepresentation_women, rankAt_rankRepresentation_women]
    exact orderRank_le_iff (mkt.prefW w) a b

end MathEconLib.Matching.MarriageMarket
