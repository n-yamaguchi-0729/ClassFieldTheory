/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldInvariantClass
import Nyll.AlgebraicCurves.Models.ConstantExtension.DivisorDescent
import Nyll.AlgebraicCurves.Models.Construction.GeometricallyIntegralOfConstants
import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoPullback
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Degree-one divisors over the full finite constant field

Construct actual proper smooth models over the finite base and its algebraic
closure. Lang and periodic Hilbert 90 give a fixed geometric degree-one divisor,
which descends along the actual projection without changing its degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A one-variable function field over its full finite constants has a divisor of degree one. -/
theorem exists_divisor_degree_one_of_finite_constants
    {k F₀ : Type} [Field k] [Finite k] [Field F₀] [Algebra k F₀]
    [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    (hfg : ∃ x : F₀, Transcendental k x ∧
      FiniteDimensional (IntermediateField.adjoin k ({x} : Set F₀)) F₀)
    (hC : ConstantsAreBase k F₀) :
    ∃ D : Divisor k F₀, Divisor.degree D = 1 := by
  let fintype : Fintype k := Fintype.ofFinite k
  obtain ⟨M₀⟩ := CurveModel.nonempty_of_perfectField k F₀ hfg
  have hgeom : GeometricallyIntegral M₀.toBase := M₀.geometricallyIntegral_of_constantsAreBase hC
  let Ω := AlgebraicClosure k
  obtain ⟨F, fieldF, algF, curveF, eftF, M, e, he⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed k M₀.toBase Ω (specMap k Ω)
  obtain ⟨D, hdeg, hfixed⟩ :=
    JacobianVarieties.Picard.exists_constantFrobenius_fixed_degree_one_divisor M₀.toBase M e he
  let baseAlg : Algebra F₀ F := M₀.constantModelAlgebra M e
  let constAlg : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
  have towerΩ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have tower₀ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
  have integralF : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
  obtain ⟨D₀, hD₀, -⟩ := M₀.existsUnique_constantFrobenius_divisor_descent M e he hC D hfixed
  refine ⟨D₀, ?_⟩
  rw [← M₀.degree_pullback_constantModel M e he hC D₀, hD₀, hdeg]

/-- Over full finite constants the actual divisor degree map is surjective onto the integers. -/
theorem degree_surjective_of_finite_constants
    {k F : Type} [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hfg : ∃ x : F, Transcendental k x ∧
      FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hC : ConstantsAreBase k F) : Function.Surjective (Divisor.degree : Divisor k F → ℤ) := by
  obtain ⟨D, hD⟩ := exists_divisor_degree_one_of_finite_constants hfg hC
  intro n
  refine ⟨n • D, ?_⟩
  rw [map_zsmul, hD, zsmul_eq_mul, mul_one, Int.cast_id]

end AlgebraicCurve
