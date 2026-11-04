/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.ForMathlib.Order.ThinChains.Centrality
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Lattice

/-!
# Central pivots in thin double chain posets

The one-sided counting bound applies to a partition by whether an element's
inclusive downset is small. Its complement has small inclusive upsets.
-/

@[expose] public section

namespace MathEconLib.Order
namespace ThinChains

variable {P R C : Type*} [PartialOrder P] [Fintype P] [Fintype R] [Fintype C]

/-- A thin double chain structure restricts to any subtype. -/
def restrict (t : ThinChains P R C) (p : P → Prop) : ThinChains {x // p x} R C where
  row := fun x => t.row x.1
  col := fun x => t.col x.1
  label_injective := by
    intro x y h
    apply Subtype.ext
    exact t.label_injective h
  row_comparable := by
    intro x y h
    rcases t.row_comparable x.1 y.1 h with hxy | hyx
    · exact Or.inl hxy
    · exact Or.inr hyx
  col_comparable := by
    intro x y h
    rcases t.col_comparable x.1 y.1 h with hxy | hyx
    · exact Or.inl hxy
    · exact Or.inr hyx

/-- Inclusive cones in a subtype inject into the corresponding original cones. -/
theorem card_subtype_downset_le (p : P → Prop) (x : {x // p x}) :
    Nat.card {y : {x // p x} // y ≤ x} ≤ Nat.card {y : P // y ≤ x.1} := by
  apply Nat.card_le_card_of_injective
    (fun y : {y : {x // p x} // y ≤ x} =>
      (⟨y.1.1, y.2⟩ : {y : P // y ≤ x.1}))
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v : {y : P // y ≤ x.1} => v.1) h

theorem card_subtype_upset_le (p : P → Prop) (x : {x // p x}) :
    Nat.card {y : {x // p x} // x ≤ y} ≤ Nat.card {y : P // x.1 ≤ y} := by
  apply Nat.card_le_card_of_injective
    (fun y : {y : {x // p x} // x ≤ y} =>
      (⟨y.1.1, y.2⟩ : {y : P // x.1 ≤ y}))
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v : {y : P // x.1 ≤ y} => v.1) h

/-- If every point has a small cone on one side, the whole poset is small. -/
theorem card_sq_le_eight_rows_cols_mul_of_cones (t : ThinChains P R C) {K : ℕ}
    (hcones : ∀ x : P,
      Nat.card {y : P // y ≤ x} ≤ K ∨ Nat.card {y : P // x ≤ y} ≤ K) :
    (Fintype.card P) ^ 2 ≤
      8 * Fintype.card R * Fintype.card C * K := by
  classical
  let smallDown : P → Prop := fun x => Nat.card {y : P // y ≤ x} ≤ K
  let a := Fintype.card {x // smallDown x}
  let b := Fintype.card {x // ¬smallDown x}
  have hcard : Fintype.card P = a + b := by
    have ha : a ≤ Fintype.card P := by
      dsimp [a]
      exact Fintype.card_subtype_le smallDown
    dsimp [a, b]
    rw [Fintype.card_subtype_compl]
    omega
  have hA : a ^ 2 ≤ 2 * Fintype.card R * Fintype.card C * K := by
    exact (t.restrict smallDown).card_sq_le_two_rows_cols_mul (K := K) (by
      intro x
      exact (card_subtype_downset_le smallDown x).trans x.2)
  have hB : b ^ 2 ≤ 2 * Fintype.card R * Fintype.card C * K := by
    exact (t.restrict fun x => ¬smallDown x).card_sq_le_two_rows_cols_mul_of_upset_le
      (K := K) (by
        intro x
        exact (card_subtype_upset_le (fun x => ¬smallDown x) x).trans
          ((hcones x.1).resolve_left x.2))
  have hsq : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  rw [hcard]
  calc
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := hsq
    _ ≤ 2 * (2 * Fintype.card R * Fintype.card C * K +
      2 * Fintype.card R * Fintype.card C * K) := by omega
    _ = 8 * Fintype.card R * Fintype.card C * K := by ring

/-- A nonempty thin double chain poset has a pivot whose smaller inclusive
cone controls the square of its cardinality. -/
theorem exists_central_pivot [Nonempty P] (t : ThinChains P R C) :
    ∃ x : P, (Fintype.card P) ^ 2 ≤
      8 * Fintype.card R * Fintype.card C *
        min (Nat.card {y : P // y ≤ x}) (Nat.card {y : P // x ≤ y}) := by
  let score : P → ℕ := fun x =>
    min (Nat.card {y : P // y ≤ x}) (Nat.card {y : P // x ≤ y})
  obtain ⟨x, hx⟩ : ∃ x : P, ∀ y : P, score y ≤ score x :=
    Finite.exists_max score
  refine ⟨x, t.card_sq_le_eight_rows_cols_mul_of_cones (K := score x) ?_⟩
  intro y
  have hscore : score y ≤ score x := hx y
  dsimp [score] at hscore
  rcases le_total (Nat.card {z : P // z ≤ y}) (Nat.card {z : P // y ≤ z}) with h | h
  · left
    simpa only [min_eq_left h] using hscore
  · right
    simpa only [min_eq_right h] using hscore

end ThinChains
end MathEconLib.Order
