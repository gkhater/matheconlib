/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.RankInput
public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable

/-! Side exchange and equal finite dimensions for explicit rank inputs. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

theorem eq_of_pref_le {M W : Type*} (A B : MarriageMarket M W)
    (hM : ∀ m a b, (A.prefM m).le a b ↔ (B.prefM m).le a b)
    (hW : ∀ w a b, (A.prefW w).le a b ↔ (B.prefW w).le a b) : A = B := by
  have hm : A.prefM = B.prefM := funext (fun m => LinearOrder.ext (hM m))
  have hw : A.prefW = B.prefW := funext (fun w => LinearOrder.ext (hW w))
  cases A
  cases B
  cases hm
  cases hw
  rfl

def castFin {a b : Nat} (h : a = b) (mkt : MarriageMarket (Fin a) (Fin a)) :
    MarriageMarket (Fin b) (Fin b) := h ▸ mkt

theorem castFin_leM {a b : Nat} (h : a = b) (mkt : MarriageMarket (Fin a) (Fin a))
    (m : Fin b) (x y : Option (Fin b)) :
    (castFin h mkt).leM m x y ↔
      mkt.leM (Fin.cast h.symm m) (x.map (Fin.cast h.symm)) (y.map (Fin.cast h.symm)) := by
  cases h
  simp [castFin]

theorem castFin_leW {a b : Nat} (h : a = b) (mkt : MarriageMarket (Fin a) (Fin a))
    (w : Fin b) (x y : Option (Fin b)) :
    (castFin h mkt).leW w x y ↔
      mkt.leW (Fin.cast h.symm w) (x.map (Fin.cast h.symm)) (y.map (Fin.cast h.symm)) := by
  cases h
  simp [castFin]

theorem castFin_galeShapley_apply {a b : Nat} (h : a = b)
    (mkt : MarriageMarket (Fin a) (Fin a)) (m w : Fin b) :
    (castFin h mkt).galeShapleyComputable m = some w ↔
      mkt.galeShapleyComputable (Fin.cast h.symm m) = some (Fin.cast h.symm w) := by
  cases h
  rfl

theorem castFin_womanGaleShapley_apply {a b : Nat} (h : a = b)
    (mkt : MarriageMarket (Fin a) (Fin a)) (m w : Fin b) :
    (castFin h mkt).womanGaleShapleyComputable m = some w ↔
      mkt.womanGaleShapleyComputable (Fin.cast h.symm m) = some (Fin.cast h.symm w) := by
  cases h
  rfl

theorem optionIndex_map_cast_val {a b : Nat} (h : a = b) (o : Option (Fin a)) :
    (optionIndex (o.map (Fin.cast h))).val = (optionIndex o).val := by
  cases h
  cases o <;> rfl

namespace RankInput

@[reducible] def swap (p : RankInput) : RankInput where
  men := p.women
  women := p.men
  women_length := p.women_length.symm
  men_row_length := by
    intro row hr
    rw [p.women_length]
    exact p.women_row_length row hr
  women_row_length := by
    intro row hr
    rw [p.women_length]
    exact p.men_row_length row hr
  men_row_nodup := p.women_row_nodup
  women_row_nodup := p.men_row_nodup

theorem swap_market (p : RankInput) : castFin p.women_length p.swap.market = p.market.symm := by
  apply eq_of_pref_le
  · intro m a b
    change (castFin p.women_length p.swap.market).leM m a b ↔ p.market.leW m a b
    rw [castFin_leM, p.swap.leM_iff, p.leW_iff]
    cases a <;> cases b <;> simp [swap, optionIndex, p.women_length]
  · intro w a b
    change (castFin p.women_length p.swap.market).leW w a b ↔ p.market.leM w a b
    rw [castFin_leW, p.swap.leW_iff, p.leM_iff]
    cases a <;> cases b <;> simp [swap, optionIndex, p.women_length]

end RankInput
end MathEconLib.Matching.MarriageMarket
