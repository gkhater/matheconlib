/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.RankChoice
public import MathEconLib.Matching.Classical.Marriage.Truncation
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.IntervalCases

/-! Rank-list implementation of the existing threshold truncation. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

def rankBand (row : List Nat) (threshold outside i score : Nat) : Nat :=
  if i = outside then 1 else if row.getD threshold 0 ≤ score then 2 else 0

def truncateRanks (row : List Nat) (threshold outside : Nat) : List Nat :=
  (row.zip (List.range row.length)).map (fun vi =>
    rankBand row threshold outside vi.2 vi.1 * (row.sum + 1) + vi.1)

def truncateRankRows (rows : List (List Nat)) (m threshold : Nat) : List (List Nat) :=
  rows.set m (truncateRanks (rows.getD m []) threshold rows.length)

theorem getD_set_same {α : Type} (xs : List α) (i : Nat) (a d : α) (hi : i < xs.length) :
    (xs.set i a).getD i d = a := by
  simp only [List.getD, List.getElem?_set_self hi, Option.getD_some]

theorem getD_set_other {α : Type} (xs : List α) (i j : Nat) (a d : α) (h : i ≠ j) :
    (xs.set i a).getD j d = xs.getD j d := by
  simp only [List.getD, List.getElem?_set_ne h]

theorem rankAt_truncateRankRows_self (rows : List (List Nat)) (m t : Nat) (hm : m < rows.length) :
    rankAt (truncateRankRows rows m t) m =
      fun j => (truncateRanks (rows.getD m []) t rows.length).getD j 0 := by
  funext j
  unfold rankAt truncateRankRows
  rw [getD_set_same _ _ _ _ hm]

theorem rankAt_truncateRankRows_other (rows : List (List Nat)) (m t i : Nat) (h : m ≠ i) :
    rankAt (truncateRankRows rows m t) i = rankAt rows i := by
  funext j
  unfold rankAt truncateRankRows
  rw [getD_set_other _ _ _ _ _ h]

@[simp] theorem truncateRanks_length (row : List Nat) (threshold outside : Nat) :
    (truncateRanks row threshold outside).length = row.length := by
  simp [truncateRanks]

private theorem member_le_sum (row : List Nat) (v : Nat) (hv : v ∈ row) : v ≤ row.sum := by
  induction row with
  | nil => cases hv
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · have h := ih hv
      simp only [List.sum_cons]
      omega

theorem rank_lt_base (row : List Nat) (i : Nat) (hi : i < row.length) :
    row.getD i 0 < row.sum + 1 := by
  rw [List.getD_eq_getElem row 0 hi]
  exact Nat.lt_succ_iff.mpr (member_le_sum row _ (List.getElem_mem hi))

theorem truncateRanks_getD (row : List Nat) (threshold outside i : Nat) (hi : i < row.length) :
    (truncateRanks row threshold outside).getD i 0 =
      rankBand row threshold outside i (row.getD i 0) * (row.sum + 1) + row.getD i 0 := by
  rw [List.getD_eq_getElem _ 0 (by simpa using hi), List.getD_eq_getElem row 0 hi]
  simp only [truncateRanks, List.getElem_map, List.getElem_zip, List.getElem_range]

theorem truncateRanks_mod (row : List Nat) (threshold outside i : Nat) (hi : i < row.length) :
    (truncateRanks row threshold outside).getD i 0 % (row.sum + 1) = row.getD i 0 := by
  rw [truncateRanks_getD row threshold outside i hi]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (rank_lt_base row i hi)

theorem truncateRanks_map_mod (row : List Nat) (threshold outside : Nat) :
    (truncateRanks row threshold outside).map (fun v => v % (row.sum + 1)) = row := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map]
    have h := truncateRanks_mod row threshold outside i hj
    rw [List.getD_eq_getElem _ 0 (by simpa using hj), List.getD_eq_getElem row 0 hj] at h
    exact h

theorem truncateRanks_nodup (row : List Nat) (threshold outside : Nat) (hnd : row.Nodup) :
    (truncateRanks row threshold outside).Nodup := by
  have h : ((truncateRanks row threshold outside).map (fun v => v % (row.sum + 1))).Nodup := by
    rw [truncateRanks_map_mod]
    exact hnd
  exact List.Nodup.of_map _ h

theorem rankBand_le_two (row : List Nat) (threshold outside i score : Nat) :
    rankBand row threshold outside i score ≤ 2 := by
  unfold rankBand
  split_ifs <;> omega

theorem rank_lex_le {B a b x y : Nat} (ha : a ≤ 2) (hb : b ≤ 2)
    (hx : x < B) (hy : y < B) :
    a * B + x ≤ b * B + y ↔ a < b ∨ a = b ∧ x ≤ y := by
  interval_cases a <;> interval_cases b <;> omega

theorem rankBand_eq_tag {n : Nat} (row : List Nat) (hlen : row.length = n + 1)
    (hnd : row.Nodup) (threshold : Fin n) (o : Option (Fin n)) :
    rankBand row threshold.val n (optionIndex o).val (row.getD (optionIndex o).val 0) =
      truncationTag (rankRowOrder row hlen hnd) threshold o := by
  cases o with
  | none => simp [rankBand, optionIndex, truncationTag]
  | some w =>
    have hne : w.val ≠ n := Nat.ne_of_lt w.is_lt
    simp only [rankBand, optionIndex, Fin.val_castSucc, hne, ↓reduceIte, truncationTag]
    rfl

theorem truncateRanks_le_iff {n : Nat} (row : List Nat) (hlen : row.length = n + 1)
    (hnd : row.Nodup) (threshold : Fin n) (a b : Option (Fin n)) :
    @LE.le _ (rankRowOrder (truncateRanks row threshold.val n)
      (by simpa using hlen) (truncateRanks_nodup _ _ _ hnd)).toLE a b ↔
    @LE.le _ (truncateOptionOrder (rankRowOrder row hlen hnd) threshold).toLE a b := by
  let : LE (Option (Fin n)) := (rankRowOrder row hlen hnd).toLE
  let := rankRowOrder row hlen hnd
  have ha : (optionIndex a).val < row.length := by rw [hlen]; exact (optionIndex a).is_lt
  have hb : (optionIndex b).val < row.length := by rw [hlen]; exact (optionIndex b).is_lt
  change (truncateRanks row threshold.val n).getD (optionIndex a).val 0 ≤
      (truncateRanks row threshold.val n).getD (optionIndex b).val 0 ↔
      truncationKey (rankRowOrder row hlen hnd) threshold a ≤
        truncationKey (rankRowOrder row hlen hnd) threshold b
  rw [truncateRanks_getD _ _ _ _ ha, truncateRanks_getD _ _ _ _ hb,
    rank_lex_le (rankBand_le_two _ _ _ _ _) (rankBand_le_two _ _ _ _ _)
      (rank_lt_base row _ ha) (rank_lt_base row _ hb),
    rankBand_eq_tag row hlen hnd threshold a, rankBand_eq_tag row hlen hnd threshold b]
  simp only [truncationKey, Prod.Lex.toLex_le_toLex]
  rfl

theorem truncateRanks_order {n : Nat} (row : List Nat) (hlen : row.length = n + 1)
    (hnd : row.Nodup) (threshold : Fin n) :
    rankRowOrder (truncateRanks row threshold.val n) (by simpa using hlen)
      (truncateRanks_nodup _ _ _ hnd) =
        truncateOptionOrder (rankRowOrder row hlen hnd) threshold := by
  apply LinearOrder.ext
  intro a b
  exact truncateRanks_le_iff row hlen hnd threshold a b

end MathEconLib.Matching.MarriageMarket
