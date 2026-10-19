/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelExtension
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.UniquePullbackConstantsEq
import Nyll.AlgebraicCurves.FunctionFields.LinearAlgebra.LinearIndependentAlgebraMap
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantFieldDegreeFormula
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusUnits
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Descent of actual Frobenius-fixed geometric divisors

The original-field embedding, generation, linear disjointness, and fixed
constants are supplied from the actual curve models and finite-field Frobenius.
Invariant geometric divisors descend uniquely, preserving their degrees.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurves.FunctionFields.Proofs
open LinearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- A Frobenius-fixed geometric divisor descends uniquely along the actual model embedding. -/
theorem existsUnique_constantFrobenius_divisor_descent (hC : ConstantsAreBase k F₀)
    (D : Divisor Ω F) (hD : φ • D = D) :
    let _ : Algebra F₀ F := M₀.constantModelAlgebra M e
    let _ : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
    let _ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
    let _ : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
    ∃! D₀ : Divisor k F₀, Divisor.pullbackConstants Ω F D₀ = D := by
  intro baseAlg constAlg towerΩ tower₀ hInt
  have hgen := M₀.adjoin_original_field_eq_top M e he
  let G := Subgroup.zpowers φ
  apply Divisor.existsUnique_pullbackConstants_eq_of_forall_smul_eq
    (IntermediateField.fg_top k F₀) hgen ?_ G ?_ ?_ D ?_
  · intro n f a hf hrel
    have hli := linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic
      k F₀ Ω F hC hf
    apply Fintype.linearIndependent_iff.mp hli a
    simpa only [Algebra.smul_def] using hrel
  · intro g hg x
    obtain ⟨i, rfl⟩ := hg
    apply MulAction.mem_fixedBy_zpow
    exact M.constantSemilinearAction_baseEmbedding M₀.toBase e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (M₀.ffEquiv x)
  · intro a ha
    apply (FiniteField.frobenius_eq_self_iff_mem_range k Ω a).mp
    exact ha φ (Subgroup.mem_zpowers φ)
  · intro g hg
    obtain ⟨i, rfl⟩ := hg
    exact MulAction.mem_fixedBy_zpow hD i

omit [Fintype k] [IsAlgClosed Ω] in
/-- The actual constant extension preserves the degree of every descended divisor. -/
theorem degree_pullback_constantModel [PerfectField k]
    (hC : ConstantsAreBase k F₀) (D : Divisor k F₀) :
    let _ : Algebra F₀ F := M₀.constantModelAlgebra M e
    let _ : Algebra k F := ((algebraMap Ω F).comp (algebraMap k Ω)).toAlgebra
    let _ : IsScalarTower k Ω F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k F₀ F := M₀.constantModel_isScalarTower M e he
    let _ : Algebra.IsIntegral F₀ F := (M₀.constantModel_isIntegral_and_adjoin M e he).1
    Divisor.degree (Divisor.pullbackConstants Ω F D) = Divisor.degree D := by
  intro baseAlg constAlg towerΩ tower₀ hInt
  have hgen := (M₀.constantModel_isIntegral_and_adjoin M e he).2
  have hconst : ∀ x : F₀, IsAlgebraic k x → x ∈ (algebraMap k F₀).range :=
    fun x hx => LdCab.mem_range_of_isAlgebraic hC x hx
  have hdeg : ConstantFieldDegreeFormula k Ω F₀ F :=
    constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver hgen hconst
  exact ConstantFieldDegreeFormula.degree_pullbackConstants D

end AlgebraicCurve.CurveModel
