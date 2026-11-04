/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.IrreducibleChains
public import MathEconLib.ForMathlib.Order.ThinChains.Pivot

/-!
# A central irreducible in a marriage market

The intrinsic join-irreducibles are thin double chains with men and women as
the two labels. Generic thin-chain counting therefore supplies a pivot.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v} (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W]

namespace StableMatching

/-- An intrinsic irreducible has a small inclusive cone on neither side unless
the total number of irreducibles is correspondingly small. -/
theorem exists_central_irreducible
    [Nonempty {μ : mkt.StableMatching // SupIrred μ}] :
    ∃ j : {μ : mkt.StableMatching // SupIrred μ},
      (Nat.card {μ : mkt.StableMatching // SupIrred μ}) ^ 2 ≤
        8 * Fintype.card M * Fintype.card W *
          min
            (Nat.card {k : {μ : mkt.StableMatching // SupIrred μ} // k ≤ j})
            (Nat.card {k : {μ : mkt.StableMatching // SupIrred μ} // j ≤ k}) := by
  classical
  let : Fintype mkt.StableMatching := by
    have hinj : Function.Injective
        (fun μ : mkt.StableMatching => fun m : M => μ.matching m) := by
      intro μ ν h
      apply ext mkt
      apply PEquiv.ext
      intro m
      exact congrFun h m
    have : Finite mkt.StableMatching := Finite.of_injective _ hinj
    exact Fintype.ofFinite _
  let : Fintype {μ : mkt.StableMatching // SupIrred μ} := inferInstance
  obtain ⟨j, hj⟩ := (irreducibleThinChains mkt).exists_central_pivot
  exact ⟨j, by simpa only [Nat.card_eq_fintype_card] using hj⟩

end StableMatching
end MarriageMarket
end MathEconLib.Matching
