/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.ForMathlib.Order.ThinChains
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting in thin double chain posets

The ordered pairs in column prefixes are counted twice: by row, where they
inject into a row maximum's downset, and by column, where their number is
quadratic in the column sizes.
-/

@[expose] public section

namespace MathEconLib.Order
namespace ThinChains

variable {P R C : Type*} [PartialOrder P] [Fintype P] [Fintype R] [Fintype C]
variable (t : ThinChains P R C)

/-- All comparable pairs inside a column, oriented downwards. -/
noncomputable def allPrefixPairs : Finset (P × P) := by
  classical
  exact Finset.univ.filter fun p => t.col p.2 = t.col p.1 ∧ p.2 ≤ p.1

/-- The pairs counted in one row. -/
noncomputable def rowPrefixFinset (r : R) : Finset (P × P) := by
  classical
  exact Finset.univ.filter fun p =>
    t.row p.1 = r ∧ t.col p.2 = t.col p.1 ∧ p.2 ≤ p.1

theorem card_rowPrefixPair_eq_finset (r : R) :
    Nat.card (t.RowPrefixPair r) = (t.rowPrefixFinset r).card := by
  classical
  change Nat.card
    {p : P × P // t.row p.1 = r ∧ t.col p.2 = t.col p.1 ∧ p.2 ≤ p.1} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Prefix pairs partition by the row of their first coordinate. -/
theorem card_allPrefixPairs_eq_sum_rows :
    (t.allPrefixPairs).card =
      ∑ r : R, (t.rowPrefixFinset r).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := t.allPrefixPairs) (t := (Finset.univ : Finset R))
    (f := fun p : P × P => t.row p.1) (by simp)
  calc
    (t.allPrefixPairs).card =
        ∑ r : R, ((t.allPrefixPairs).filter fun p => t.row p.1 = r).card := by
          simpa using h
    _ = ∑ r : R, (t.rowPrefixFinset r).card := by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      ext p
      simp [allPrefixPairs, rowPrefixFinset, and_assoc, and_left_comm, and_comm]

/-- If every inclusive downset has size below `K`, every row contributes
fewer than `K` column-prefix pairs. -/
theorem card_rowPrefixFinset_lt_of_downset_lt {K : ℕ} (hK : 0 < K)
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} < K) (r : R) :
    (t.rowPrefixFinset r).card < K := by
  classical
  by_cases hr : (t.rowFiber r).Nonempty
  · obtain ⟨v, _, hcard⟩ := t.rowPrefixPairs_card_le_downset hr
    rw [← t.card_rowPrefixPair_eq_finset r]
    exact hcard.trans_lt (hdown v)
  · have hempty : t.rowPrefixFinset r = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hrow : t.row p.1 = r := by
        simpa [rowPrefixFinset] using (Finset.mem_filter.mp hp).2.1
      exact hr ⟨p.1, t.mem_rowFiber.mpr hrow⟩
    simpa only [hempty, Finset.card_empty] using hK

/-- One-sided counting: the total number of column-prefix pairs is bounded
by rows times the maximum allowed inclusive downset size. -/
theorem card_allPrefixPairs_lt_rows_mul [Nonempty R] {K : ℕ} (hK : 0 < K)
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} < K) :
    (t.allPrefixPairs).card < Fintype.card R * K := by
  rw [t.card_allPrefixPairs_eq_sum_rows]
  calc
    (∑ r : R, (t.rowPrefixFinset r).card) < ∑ _r : R, K := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro r _
      exact t.card_rowPrefixFinset_lt_of_downset_lt hK hdown r
    _ = Fintype.card R * K := by simp

/-- The fibre of one column. -/
noncomputable def colFiber (c : C) : Finset P := by
  classical
  exact Finset.univ.filter fun x => t.col x = c

/-- Ordered prefix pairs in one column. -/
noncomputable def colPrefixFinset (c : C) : Finset (P × P) := by
  classical
  exact (t.allPrefixPairs).filter fun p => t.col p.1 = c

/-- A column of length `b` contributes at least `b²/2` ordered prefix pairs. -/
theorem card_colFiber_sq_le_two_prefix (c : C) :
    (t.colFiber c).card ^ 2 ≤ 2 * (t.colPrefixFinset c).card := by
  classical
  let s := t.colFiber c
  let d := t.colPrefixFinset c
  have hsubset : s.product s ⊆ d ∪ d.image Prod.swap := by
    rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have hcx : t.col x = c := by simpa [s, colFiber] using hx
    have hcy : t.col y = c := by simpa [s, colFiber] using hy
    rcases t.col_comparable x y (hcx.trans hcy.symm) with hxy | hyx
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(y, x), ?_, rfl⟩
      simp [d, colPrefixFinset, allPrefixPairs, hcx, hcy, hxy]
    · apply Finset.mem_union_left
      simp [d, colPrefixFinset, allPrefixPairs, hcx, hcy, hyx]
  have hswap : (d.image Prod.swap).card = d.card := by
    apply Finset.card_image_of_injective
    intro p q h
    simpa only [Prod.swap_swap] using congrArg Prod.swap h
  calc
    (t.colFiber c).card ^ 2 = (s.product s).card := by
      simp [s, Finset.card_product, pow_two]
    _ ≤ (d ∪ d.image Prod.swap).card := Finset.card_le_card hsubset
    _ ≤ d.card + (d.image Prod.swap).card := Finset.card_union_le _ _
    _ = 2 * (t.colPrefixFinset c).card := by
      rw [hswap]
      change d.card + d.card = 2 * d.card
      omega

/-- The poset partitions into column fibres. -/
theorem card_eq_sum_colFiber :
    Fintype.card P = ∑ c : C, (t.colFiber c).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset P)) (t := (Finset.univ : Finset C))
    (f := t.col) (by simp)
  simpa only [Finset.card_univ, colFiber, Finset.mem_univ, Finset.filter_true] using h

/-- Prefix pairs partition by their column. -/
theorem card_allPrefixPairs_eq_sum_cols :
    (t.allPrefixPairs).card =
      ∑ c : C, (t.colPrefixFinset c).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := t.allPrefixPairs) (t := (Finset.univ : Finset C))
    (f := fun p : P × P => t.col p.1) (by simp)
  simpa only [colPrefixFinset] using h

/-- Squared poset size is at most twice column count times prefix-pair count. -/
theorem card_sq_le_two_cols_mul_prefix :
    (Fintype.card P) ^ 2 ≤
      2 * Fintype.card C * (t.allPrefixPairs).card := by
  have hcs : (∑ c : C, (t.colFiber c).card) ^ 2 ≤
      Fintype.card C * ∑ c : C, (t.colFiber c).card ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset C))
      (f := fun c => (t.colFiber c).card))
  have hcol : (∑ c : C, (t.colFiber c).card ^ 2) ≤
      ∑ c : C, 2 * (t.colPrefixFinset c).card := by
    apply Finset.sum_le_sum
    intro c _
    exact t.card_colFiber_sq_le_two_prefix c
  calc
    (Fintype.card P) ^ 2 =
        (∑ c : C, (t.colFiber c).card) ^ 2 := by rw [t.card_eq_sum_colFiber]
    _ ≤ Fintype.card C * ∑ c : C, (t.colFiber c).card ^ 2 := hcs
    _ ≤ Fintype.card C * ∑ c : C, 2 * (t.colPrefixFinset c).card :=
      Nat.mul_le_mul_left _ hcol
    _ = 2 * Fintype.card C * (t.allPrefixPairs).card := by
      rw [← Finset.mul_sum, ← t.card_allPrefixPairs_eq_sum_cols]
      simp only [mul_assoc, mul_comm, mul_left_comm]

/-- One-sided quadratic counting bound for inclusive downsets. -/
theorem card_sq_lt_two_rows_cols_mul [Nonempty R] [Nonempty C]
    (t : ThinChains P R C) {K : ℕ} (hK : 0 < K)
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} < K) :
    (Fintype.card P) ^ 2 <
      2 * Fintype.card R * Fintype.card C * K := by
  have hE := card_allPrefixPairs_lt_rows_mul t hK hdown
  have hC : 0 < 2 * Fintype.card C := by
    have := Fintype.card_pos (α := C)
    omega
  have hmul := mul_lt_mul_of_pos_left hE hC
  calc
    (Fintype.card P) ^ 2 ≤
        2 * Fintype.card C * (t.allPrefixPairs).card :=
      t.card_sq_le_two_cols_mul_prefix
    _ < 2 * Fintype.card C * (Fintype.card R * K) := hmul
    _ = 2 * Fintype.card R * Fintype.card C * K := by
      simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Non-strict row bound, retaining the exact constant for the pivot theorem. -/
theorem card_rowPrefixFinset_le_of_downset_le {K : ℕ}
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} ≤ K) (r : R) :
    (t.rowPrefixFinset r).card ≤ K := by
  classical
  by_cases hr : (t.rowFiber r).Nonempty
  · obtain ⟨v, _, hcard⟩ := t.rowPrefixPairs_card_le_downset hr
    rw [← t.card_rowPrefixPair_eq_finset r]
    exact hcard.trans (hdown v)
  · have hempty : t.rowPrefixFinset r = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hrow : t.row p.1 = r := by
        simpa [rowPrefixFinset] using (Finset.mem_filter.mp hp).2.1
      exact hr ⟨p.1, t.mem_rowFiber.mpr hrow⟩
    simp [hempty]

theorem card_allPrefixPairs_le_rows_mul {K : ℕ}
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} ≤ K) :
    (t.allPrefixPairs).card ≤ Fintype.card R * K := by
  rw [t.card_allPrefixPairs_eq_sum_rows]
  calc
    (∑ r : R, (t.rowPrefixFinset r).card) ≤ ∑ _r : R, K := by
      apply Finset.sum_le_sum
      intro r _
      exact t.card_rowPrefixFinset_le_of_downset_le hdown r
    _ = Fintype.card R * K := by simp

/-- Exact non-strict one-sided quadratic bound. -/
theorem card_sq_le_two_rows_cols_mul (t : ThinChains P R C) {K : ℕ}
    (hdown : ∀ x : P, Nat.card {y : P // y ≤ x} ≤ K) :
    (Fintype.card P) ^ 2 ≤
      2 * Fintype.card R * Fintype.card C * K := by
  have hE := card_allPrefixPairs_le_rows_mul t hdown
  calc
    (Fintype.card P) ^ 2 ≤
        2 * Fintype.card C * (t.allPrefixPairs).card :=
      t.card_sq_le_two_cols_mul_prefix
    _ ≤ 2 * Fintype.card C * (Fintype.card R * K) :=
      Nat.mul_le_mul_left _ hE
    _ = 2 * Fintype.card R * Fintype.card C * K := by
      simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Reversing the order exchanges inclusive downsets and upsets. -/
def dual (t : ThinChains P R C) : ThinChains Pᵒᵈ R C where
  row := t.row
  col := t.col
  label_injective := t.label_injective
  row_comparable := by
    intro x y h
    rcases t.row_comparable x y h with hxy | hyx
    · exact Or.inr hxy
    · exact Or.inl hyx
  col_comparable := by
    intro x y h
    rcases t.col_comparable x y h with hxy | hyx
    · exact Or.inr hxy
    · exact Or.inl hyx

/-- Exact one-sided quadratic bound for inclusive upsets. -/
theorem card_sq_le_two_rows_cols_mul_of_upset_le (t : ThinChains P R C) {K : ℕ}
    (hup : ∀ x : P, Nat.card {y : P // x ≤ y} ≤ K) :
    (Fintype.card P) ^ 2 ≤
      2 * Fintype.card R * Fintype.card C * K := by
  have hdual : ∀ x : Pᵒᵈ, Nat.card {y : Pᵒᵈ // y ≤ x} ≤ K := by
    intro x
    exact hup x
  simpa using (t.dual.card_sq_le_two_rows_cols_mul hdual)

end ThinChains
end MathEconLib.Order
