/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.GaloisPresentationValue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteGaloisPresentation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantFrobenius
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient

/-!
# Arithmetic Frobenius under the native constant-field presentation

The abstract degree-one Frobenius acts on the actual constant extension
as its arithmetic Frobenius. The comparison uses the ambient action and
the full constant degree, so its normalization is fixed concretely.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The abstract arithmetic Frobenius becomes the actual full-constant Frobenius. -/
theorem fullConstant_presentedFrobenius (n : ℕ) [NeZero n] :
    let Ω := SeparableClosure K
    let E := fullConstantDegreeStage k K Ω n
    let H := intrinsicFiniteAbstractBase K
    let T := finiteGaloisAbstractExtension K E
    let eE := finiteGaloisFixedFieldEquivOfEmbedding K E E.toIntermediateField.val
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω T.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let hF : Module.finrank K (abstractFixedField K Ω H.field) = 1 := by
      rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq, Module.finrank_self]
    ((ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
      (K := K) (F := abstractFixedField K Ω H.field)
      (E := abstractFixedField K Ω T.field) hF).trans (AlgEquiv.autCongr eE).symm)
      (abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
        (T.extensionQuotientMulEquiv.symm
          ((fullConstantDegreeData k K Ω).unramifiedFrobenius
            (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω))
            T.field T.below))) = fullConstantDegreeFrobenius k K Ω n := by
  intro Ω E H T eE aFE hKFE hF
  let D := fullConstantDegreeData k K Ω
  let HR := H.toFiniteResidueAbstractField D
  let σ : H.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective HR (Multiplicative.ofAdd (1 : ZHat)))
  have hσ : D.normalizedDegree HR σ = Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec (D.normalizedDegree_surjective HR (Multiplicative.ofAdd (1 : ZHat)))
  have hres : (HR.residueDegree : ℕ) = 1 := by
    change ((intrinsicFiniteAbstractBase K).residueDegree D : ℕ) = 1
    rw [intrinsicFiniteAbstractBase_eq_base, FiniteAbstractField.base_residueDegree]
    rfl
  have hdeg : D.degree σ.val = Multiplicative.ofAdd (1 : ZHat) := by
    apply Multiplicative.ext
    have hd := D.residueDegree_nsmul_normalizedDegree HR σ
    rw [hres, one_nsmul, hσ] at hd
    exact hd.symm
  have hq : T.extensionQuotientMulEquiv.symm
      (D.unramifiedFrobenius HR T.field T.below) =
        QuotientGroup.mk' (extensionSubgroup H.field T.field T.below) σ := rfl
  rw [hq]
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hv := ClassFieldTheory.galoisPresentation_mk_apply_val
    K E Ω H.field T.field T.below T.normal eE hF σ x
  change _ = σ.val (x : Ω) at hv
  exact hv.trans ((AlgEquiv.restrictNormal_commutes σ.val E x).symm.trans
    (congrArg (fun τ : Gal(E/K) => (τ x : Ω))
      (fullConstantDegreeData_one_restrict k K Ω σ.val hdeg n)))

end FunctionField
