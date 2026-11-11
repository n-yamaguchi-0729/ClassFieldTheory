/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteReciprocityDataComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNaturality

/-!
# Finite ray reciprocity and the named absolute Artin map

The finite reciprocity datum has arithmetic normalization; the existing
named absolute map has geometric normalization. Their pointwise comparison
therefore contains an explicit inverse. Both maps retain their original values.
-/

@[expose] public section

open scoped NumberField
open GlobalClassFieldTheory.Reciprocity
open ClassFieldTheory

noncomputable section

namespace ClassFieldTheory.FiniteAbelianReciprocityData

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (maximalAbelianExtension K)]
  [IsScalarTower K L (maximalAbelianExtension K)]

/-- For any supplied finite reciprocity datum and its actual finite-field
embedding, the ray value is the inverse of the named absolute Artin restriction. -/
theorem ideleClassArtin_eq_inv_mathlibGlobalArtin_restrict
    (D : FiniteAbelianReciprocityData K L) (x : IdeleClassGroup K) :
    D.ideleClassArtin x =
      (AlgEquiv.restrictNormalHom L
        (mathlibAbelianizationToMaximal K
          (mathlibGlobalArtin K
            (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K x))))⁻¹ := by
  have hfinite := mathlibGlobalArtin_finiteProjection_of_scalarTower
    (K := K) L (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K x)
  have hgeo : AlgEquiv.restrictNormalHom L
      (mathlibAbelianizationToMaximal K
        (mathlibGlobalArtin K
          (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K x))) =
      globalNormResidueMonoidHom K L x := by
    simpa only [ContinuousMulEquiv.symm_apply_apply,
      globalIdeleClassArtinMonoidHom_eq_globalNormResidueMonoidHom] using hfinite
  exact (D.ideleClassArtin_apply x).trans
    ((arithmeticGlobalNormResidueMonoidHom_apply K L x).trans
      (congrArg (fun σ : L ≃ₐ[K] L => σ⁻¹) hgeo.symm))

end ClassFieldTheory.FiniteAbelianReciprocityData
