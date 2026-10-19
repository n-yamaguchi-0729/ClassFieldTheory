/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldLang
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
import Nyll.SchemeTheory.Morphisms.FiniteExtensionPoint

/-!
# Lang surjectivity for the canonical action on geometric Picard classes

Identify the constructed Picard Frobenius with the canonical action on the
actual geometric function field. Passing to a finite constant field carrying
a rational point removes the pointed-curve hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap k Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

/-- All positive powers of canonical Picard Frobenius satisfy Lang for a pointed curve. -/
theorem pic0_constantFrobenius_pow_sub_surjective_of_point
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun z : Pic0 Ω F =>
      (M.constantSemilinearAction c eC heC
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ^ n • z - z) := by
  obtain ⟨g, θ, hproj, hbase, -, hfun, hLang⟩ :=
    exists_pic0_frobenius_lang c ε M eC heC
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  have hθ : θ = M.coefficientIso c eC σ :=
    M.baseChange_iso_eq c eC heC θ (M.coefficientIso c eC σ)
      (hproj.trans (M.coefficientIso_fst c eC σ).symm)
      (hbase.trans (M.coefficientIso_base c eC heC σ).symm)
  subst θ
  have hg : g = M.constantSemilinearAction c eC heC σ :=
    M.semilinearAut_eq_of_germ_action _ _ _ hfun (M.constantSemilinearAction_germ c eC heC σ)
  exact hg ▸ hLang n hn

/-- Positive Frobenius powers satisfy Lang on Picard classes without a rational point assumption. -/
theorem pic0_constantFrobenius_pow_sub_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun z : Pic0 Ω F =>
      (M.constantSemilinearAction c eC heC
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ^ n • z - z) := by
  have : Nonempty C := Nonempty.map
    (fun x : M.C => pullback.fst c (specMap k Ω) (eC.hom x)) inferInstance
  obtain ⟨E, hE, p, _, hp⟩ := exists_point_finite_intermediateField k Ω c
  let : Module.Finite k E := hE
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := k) E
  let cE := pullback.snd c (specMap k E)
  let εE : SchemeHomOver (𝟙 (Spec (CommRingCat.of E))) cE :=
    ⟨pullback.lift p (𝟙 (Spec (CommRingCat.of E))) (by
      rw [Category.id_comp]
      exact hp), pullback.lift_snd _ _ _⟩
  have hLang := pic0_constantFrobenius_pow_sub_surjective_of_point cE M
    (M.constantTowerModelIso k E Ω c eC) (M.constantTowerModelIso_base k E Ω c eC heC)
    εE n hn
  have hF := M.constantSemilinearAction_frobenius_tower k E Ω c eC heC
  let g := M.constantSemilinearAction c eC heC (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
  apply CyclicAction.surjective_sub_of_surjective_sub_pow (g ^ n) (Module.finrank k E)
  rw [hF] at hLang
  simpa only [← pow_mul, Nat.mul_comm (Module.finrank k E) n] using hLang

end JacobianVarieties.Picard
