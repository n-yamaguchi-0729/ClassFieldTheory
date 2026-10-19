/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegreeSurjective
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormalizedDegreeOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower

/-!
# Degree-one norm witnesses transported by actual field isomorphisms

The actual idele-class base-change map induced by a field isomorphism preserves
normalized degree. Norm transitivity and the degree-one norm formula give
degree-one classes in both fields with the same norm to the common base.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable (k F L M : Type) [Field k] [Finite k] [Field F] [Field L] [Field M]
    [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra F L] [Algebra F M] [IsScalarTower k F L] [IsScalarTower k F M]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]

/-- An actual isomorphism of finite function-field extensions supplies normalized
degree-one idele classes with equal norms to the common base. -/
theorem exists_normalizedDegree_one_norm_eq_of_algEquiv (φ : L ≃ₐ[F] M) :
    let _ : FiniteDimensional F M := φ.toLinearEquiv.finiteDimensional
    let _ : Algebra.IsSeparable F M := AlgEquiv.Algebra.isSeparable φ
    let _ : AlgebraicCurve.HasPrincipalDivisors k F :=
      (isCurveOver k F).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k F L).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k M :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k F M).toHasPrincipalDivisors
    ∃ (cL : IdeleClassGroup k L) (cM : IdeleClassGroup k M),
      (normalizedDegree (k := k) (K := L) cL).toAdd = 1 ∧
      (normalizedDegree (k := k) (K := M) cM).toAdd = 1 ∧
      norm (k := k) (K := F) (L := L) cL =
        norm (k := k) (K := F) (L := M) cM := by
  intro hFM hFMsep hFprincipal hLprincipal hMprincipal
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k F L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hLff : FunctionField k L := presentation.property.2
  let aLM : Algebra L M := φ.toRingHom.toAlgebra
  have hFLM : IsScalarTower F L M :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hkLM : IsScalarTower k L M := IsScalarTower.to₁₃₄ k F L M
  let φL : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (R := L) (f := φ.toRingEquiv) (fun _ => rfl)
  have hLMfinite : FiniteDimensional L M := φL.toLinearEquiv.finiteDimensional
  have hLMsep : Algebra.IsSeparable L M := AlgEquiv.Algebra.isSeparable φL
  have hdegree : Module.finrank L M = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr φ.bijective
  obtain ⟨cL, hcL⟩ := exists_normalizedDegree_one (k := k) (K := L)
  let cM : IdeleClassGroup k M := baseChange (k := k) (K := L) (L := M) cL
  have hcM : normalizedDegree (k := k) (K := M) cM = Multiplicative.ofAdd 1 :=
    (normalizedDegree_baseChange_of_finrank_one hdegree cL).trans hcL
  refine ⟨cL, cM, congrArg Multiplicative.toAdd hcL, congrArg Multiplicative.toAdd hcM, ?_⟩
  have hnorm := norm_trans (k := k) (K := F) (L := L) (M := M) cM
  change norm (k := k) (K := F) (L := L)
      (norm (k := k) (K := L) (L := M) (baseChange (k := k) (K := L) (L := M) cL)) =
    norm (k := k) (K := F) (L := M) cM at hnorm
  rw [norm_baseChange, hdegree, pow_one] at hnorm
  exact hnorm

end FunctionField.IdeleClassGroup
