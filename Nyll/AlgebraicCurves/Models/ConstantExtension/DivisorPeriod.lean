/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PlacePeriod
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
import Nyll.GaloisCohomology.Cyclic.PeriodicNorm

/-!
# Positive Frobenius periods of divisors and Picard classes

Finite support turns the actual periods of geometric places into a common
positive period for every divisor. Consequently every full or degree-zero
geometric Picard class belongs to an actual periodic subgroup.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve CyclicAction

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c] [IsSeparated c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

local notation "φ" =>
  M.constantSemilinearAction c e he (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Every actual geometric divisor is fixed by a positive Frobenius power. -/
theorem exists_constantFrobenius_divisor_period (D : Divisor Ω F) :
    ∃ n : ℕ, n ≠ 0 ∧ φ ^ n • D = D := by
  induction D using Finsupp.induction with
  | zero => exact ⟨1, Nat.one_ne_zero, smul_zero _⟩
  | single_add v a D _ _ ih =>
    obtain ⟨n, hn, hv⟩ := M.exists_constantFrobenius_place_period c e he v
    obtain ⟨m, hm, hD⟩ := ih
    have hs : φ ^ n • Finsupp.single v a = (Finsupp.single v a : Divisor Ω F) := by
      rw [SemilinearAut.smul_single, hv]
    have hs' : φ ^ (n * m) • Finsupp.single v a =
        (Finsupp.single v a : Divisor Ω F) := periodicSubgroup_le_mul φ n m hs
    have hD' : φ ^ (n * m) • D = D := by
      rw [Nat.mul_comm]
      exact periodicSubgroup_le_mul φ m n hD
    exact ⟨n * m, mul_ne_zero hn hm, (smul_add _ _ _).trans (congrArg₂ (· + ·) hs' hD')⟩

/-- Every actual full geometric Picard class has positive Frobenius period. -/
theorem exists_constantFrobenius_picard_period (x : Pic Ω F) :
    ∃ n : ℕ, n ≠ 0 ∧ φ ^ n • x = x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  obtain ⟨n, hn, hD⟩ := M.exists_constantFrobenius_divisor_period c e he D
  exact ⟨n, hn, (SemilinearAut.pic_smul_mk (φ ^ n) D).trans (congrArg H1Gm.mk hD)⟩

/-- Every actual degree-zero geometric Picard class has positive Frobenius period. -/
theorem exists_constantFrobenius_pic0_period (x : Pic0 Ω F) :
    ∃ n : ℕ, n ≠ 0 ∧ φ ^ n • x = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨n, hn, hD⟩ := M.exists_constantFrobenius_divisor_period c e he D
  refine ⟨n, hn, ?_⟩
  rw [SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext hD)

end AlgebraicCurve.CurveModel
