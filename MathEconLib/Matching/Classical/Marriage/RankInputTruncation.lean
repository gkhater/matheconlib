/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.RankTruncation
public import MathEconLib.Matching.Classical.Marriage.RankSymmetry

/-! Truncating an explicit input realizes the existing market transformation. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

theorem truncateMan_leM_self {M W : Type*} [DecidableEq M]
    (mkt : MarriageMarket M W) (m : M) (threshold : W) (a b : Option W) :
    (mkt.truncateMan m threshold).leM m a b ↔
      @LE.le _ (truncateOptionOrder (mkt.prefM m) threshold).toLE a b := by
  change @LE.le _ ((mkt.truncateMan m threshold).prefM m).toLE a b ↔ _
  rw [mkt.truncateMan_prefM_self]

namespace RankInput

@[reducible] def truncated (p : RankInput) (m threshold : Fin p.men.length) : RankInput where
  men := truncateRankRows p.men m.val threshold.val
  women := p.women
  women_length := by simpa only [truncateRankRows, List.length_set] using p.women_length
  men_row_length := by
    intro row hr
    change row ∈ p.men.set m.val _ at hr
    simp only [truncateRankRows, List.length_set]
    rcases List.mem_or_eq_of_mem_set hr with hr | rfl
    · exact p.men_row_length row hr
    · rw [truncateRanks_length, List.getD_eq_get p.men [] m]
      exact p.men_row_length _ (List.get_mem _ _)
  women_row_length := by
    intro row hr
    simpa only [truncateRankRows, List.length_set] using p.women_row_length row hr
  men_row_nodup := by
    intro row hr
    change row ∈ p.men.set m.val _ at hr
    rcases List.mem_or_eq_of_mem_set hr with hr | rfl
    · exact p.men_row_nodup row hr
    · apply truncateRanks_nodup
      rw [List.getD_eq_get p.men [] m]
      exact p.men_row_nodup _ (List.get_mem _ _)
  women_row_nodup := p.women_row_nodup

theorem truncated_length (p : RankInput) (m threshold : Fin p.men.length) :
    (p.truncated m threshold).men.length = p.men.length := by
  simp only [truncateRankRows, List.length_set]

theorem truncated_market (p : RankInput) (m threshold : Fin p.men.length) :
    castFin (p.truncated_length m threshold) (p.truncated m threshold).market =
      p.market.truncateMan m threshold := by
  apply eq_of_pref_le
  · intro i a b
    change (castFin (p.truncated_length m threshold) (p.truncated m threshold).market).leM i a b ↔
      (p.market.truncateMan m threshold).leM i a b
    rw [castFin_leM, (p.truncated m threshold).leM_iff]
    simp only [Fin.val_cast, optionIndex_map_cast_val]
    by_cases hi : i = m
    · subst i
      rw [truncateMan_leM_self]
      change rankAt (truncateRankRows p.men m.val threshold.val) m.val (optionIndex a).val ≤
          rankAt (truncateRankRows p.men m.val threshold.val) m.val (optionIndex b).val ↔ _
      simp only [rankAt_truncateRankRows_self p.men m.val threshold.val m.is_lt,
        List.getD_eq_get p.men [] m]
      exact truncateRanks_le_iff (p.men.get m) (p.men_row_length _ (List.get_mem _ _))
        (p.men_row_nodup _ (List.get_mem _ _)) threshold a b
    · rw [p.market.truncateMan_leM_of_ne m i threshold hi, p.leM_iff]
      have hval : m.val ≠ i.val := by
        intro h
        exact hi (Fin.ext h.symm)
      exact Iff.of_eq (by
        change (rankAt (truncateRankRows p.men m.val threshold.val) i.val (optionIndex a).val ≤
          rankAt (truncateRankRows p.men m.val threshold.val) i.val (optionIndex b).val) = _
        rw [rankAt_truncateRankRows_other p.men m.val threshold.val i.val hval])
  · intro w a b
    change (castFin (p.truncated_length m threshold) (p.truncated m threshold).market).leW w a b ↔
      (p.market.truncateMan m threshold).leW w a b
    rw [castFin_leW, (p.truncated m threshold).leW_iff, truncateMan_leW, p.leW_iff]
    simp only [Fin.val_cast, optionIndex_map_cast_val]

end RankInput
end MathEconLib.Matching.MarriageMarket
