/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.RankInput
public import MathEconLib.Choice.FiniteOption

/-! A list-based rank selector, suitable for polynomial-time compilation. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

def preferHigher (score : Nat → Nat) (best candidate : Nat) : Nat :=
  if score best < score candidate then candidate else best

theorem preferHigher_mem (score : Nat → Nat) (best candidate : Nat) :
    preferHigher score best candidate = best ∨ preferHigher score best candidate = candidate := by
  unfold preferHigher
  split_ifs <;> simp

theorem score_le_preferHigher_left (score : Nat → Nat) (best candidate : Nat) :
    score best ≤ score (preferHigher score best candidate) := by
  unfold preferHigher
  split_ifs <;> omega

theorem score_le_preferHigher_right (score : Nat → Nat) (best candidate : Nat) :
    score candidate ≤ score (preferHigher score best candidate) := by
  unfold preferHigher
  split_ifs <;> omega

def rankBest (rows : List (List Nat)) (i outside : Nat) (candidates : List Nat) : Nat :=
  candidates.foldl (preferHigher (rankAt rows i)) outside

theorem rankBest_mem (rows : List (List Nat)) (i outside : Nat) (candidates : List Nat) :
    rankBest rows i outside candidates = outside ∨ rankBest rows i outside candidates ∈ candidates := by
  induction candidates generalizing outside with
  | nil => exact Or.inl rfl
  | cons e es ih =>
    change rankBest rows i (preferHigher (rankAt rows i) outside e) es = outside ∨
      rankBest rows i (preferHigher (rankAt rows i) outside e) es ∈ e :: es
    rcases ih (preferHigher (rankAt rows i) outside e) with h | h
    · rw [h]
      rcases preferHigher_mem (rankAt rows i) outside e with heq | heq
      · exact Or.inl heq
      · exact Or.inr (by simp [heq])
    · exact Or.inr (List.mem_cons_of_mem e h)

theorem rankBest_ge_outside (rows : List (List Nat)) (i outside : Nat) (candidates : List Nat) :
    rankAt rows i outside ≤ rankAt rows i (rankBest rows i outside candidates) := by
  induction candidates generalizing outside with
  | nil => exact le_rfl
  | cons e es ih =>
    exact (score_le_preferHigher_left (rankAt rows i) outside e).trans
      (ih (preferHigher (rankAt rows i) outside e))

theorem rankBest_ge_mem (rows : List (List Nat)) (i outside : Nat) (candidates : List Nat)
    (e : Nat) (he : e ∈ candidates) :
    rankAt rows i e ≤ rankAt rows i (rankBest rows i outside candidates) := by
  induction candidates generalizing outside with
  | nil => cases he
  | cons c cs ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact (score_le_preferHigher_right (rankAt rows i) outside e).trans
        (rankBest_ge_outside rows i (preferHigher (rankAt rows i) outside e) cs)
    · exact ih (preferHigher (rankAt rows i) outside c) he

/-- The list selector computes the existing finite-option choice, rather
than defining a different preference rule. -/
theorem rankBest_eq_bestOptionIndex {n : Nat} (row : List Nat)
    (hlen : row.length = n + 1) (hnd : row.Nodup) (candidates : List (Fin n)) :
    rankBest [row] 0 n (candidates.map Fin.val) =
      (optionIndex (MathEconLib.Choice.ChoiceFunction.bestOption
        (rankRowOrder row hlen hnd) candidates.toFinset)).val := by
  let pref := rankRowOrder row hlen hnd
  let best := MathEconLib.Choice.ChoiceFunction.bestOption pref candidates.toFinset
  let r := rankBest [row] 0 n (candidates.map Fin.val)
  have hrmem : r = n ∨ r ∈ candidates.map Fin.val := rankBest_mem _ _ _ _
  have hrlt : r < n + 1 := by
    rcases hrmem with h | h
    · omega
    · obtain ⟨j, _, hj⟩ := List.mem_map.mp h
      have := j.is_lt
      omega
  let ri : Fin row.length := ⟨r, by rw [hlen]; exact hrlt⟩
  let bi : Fin row.length := Fin.cast hlen.symm (optionIndex best)
  have hrscore : row.getD r 0 ≤ row.getD (optionIndex best).val 0 := by
    rcases hrmem with hrn | hrc
    · have hle := MathEconLib.Choice.ChoiceFunction.le_bestOption pref candidates.toFinset
        (MathEconLib.Choice.ChoiceFunction.none_mem_optionMenu _)
      change row.getD n 0 ≤ row.getD (optionIndex best).val 0 at hle
      simpa only [hrn] using hle
    · obtain ⟨j, hj, hjval⟩ := List.mem_map.mp hrc
      have hle := MathEconLib.Choice.ChoiceFunction.le_bestOption pref candidates.toFinset
        (MathEconLib.Choice.ChoiceFunction.some_mem_optionMenu.mpr (List.mem_toFinset.mpr hj))
      change row.getD j.val 0 ≤ row.getD (optionIndex best).val 0 at hle
      simpa only [hjval] using hle
  have hbscore : row.getD (optionIndex best).val 0 ≤ row.getD r 0 := by
    have hmem := MathEconLib.Choice.ChoiceFunction.bestOption_mem pref candidates.toFinset
    rcases MathEconLib.Choice.ChoiceFunction.mem_optionMenu.mp hmem with hnone | ⟨j, hj, hjbest⟩
    · change best = none at hnone
      rw [hnone]
      exact rankBest_ge_outside [row] 0 n (candidates.map Fin.val)
    · have h := rankBest_ge_mem [row] 0 n (candidates.map Fin.val) j.val
        (List.mem_map.mpr ⟨j, List.mem_toFinset.mp hj, rfl⟩)
      change some j = best at hjbest
      rw [← hjbest]
      exact h
  have hscore := le_antisymm hrscore hbscore
  have hget : row.get ri = row.get bi := by
    rw [← List.getD_eq_get row 0 ri, ← List.getD_eq_get row 0 bi]
    exact hscore
  exact congrArg (fun i : Fin row.length => i.val) (hnd.get_inj_iff.mp hget)

end MathEconLib.Matching.MarriageMarket
