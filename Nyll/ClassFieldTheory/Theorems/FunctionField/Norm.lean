/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteNormProperties
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.OnePlaceNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteBaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower

/-!
# Norm and inclusion formulas for arbitrary finite function-field extensions
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L]

/-- On a class represented by an idele, the public norm is the actual completed norm product. -/
theorem ideleClassNorm_mk :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ a : _root_.FunctionField.IdeleGroup k L,
      ideleClassNorm k K L (QuotientGroup.mk a) =
        QuotientGroup.mk (_root_.FunctionField.IdeleGroup.norm (K := K) (L := L) a) := by
  intro hK hL a
  rfl

/-- The public norm agrees with the original separable class norm whenever applicable. -/
theorem ideleClassNorm_eq_norm [Algebra.IsSeparable K L] :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    (ideleClassNorm k K L).toMonoidHom =
      _root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := L) := by
  intro hK hL
  exact _root_.FunctionField.IdeleClassGroup.finiteNorm_eq_norm

/-- The public norm of a one-place class is the one-place class of its local norm. -/
theorem ideleClassNorm_placeIdele (w : AlgebraicCurve.Place k L) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ x : w.adicCompletionˣ,
      ideleClassNorm k K L
        (QuotientGroup.mk (_root_.FunctionField.IdeleGroup.placeIdele w x)) =
      QuotientGroup.mk (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K)
        (_root_.FunctionField.IdeleGroup.localNorm (K := K) w x)) := by
  intro hK hL x
  rw [ideleClassNorm_mk, _root_.FunctionField.IdeleGroup.norm_placeIdele]

/-- Actual class norms preserve degree relative to the common constant field. -/
theorem ideleClassNorm_degree :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k L,
      _root_.FunctionField.IdeleClassGroup.degree (k := k) (K := K) (ideleClassNorm k K L c) =
        _root_.FunctionField.IdeleClassGroup.degree (k := k) (K := L) c := by
  intro hK hL c
  exact _root_.FunctionField.IdeleClassGroup.degree_finiteNorm c

/-- The public inclusion applies the actual maps of completions to an idele representative. -/
theorem ideleClassInclusion_mk :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ a : _root_.FunctionField.IdeleGroup k K,
      ideleClassInclusion k K L (QuotientGroup.mk a) =
        QuotientGroup.mk
          (_root_.FunctionField.IdeleGroup.baseChange (K := K) (L := L) a) := by
  intro hK hL a
  rfl

/-- Norm after inclusion is the actual extension-degree power. -/
theorem ideleClassNorm_inclusion :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K,
      ideleClassNorm k K L (ideleClassInclusion k K L c) =
        c ^ Module.finrank K L := by
  intro hK hL c
  exact _root_.FunctionField.IdeleClassGroup.finiteNorm_baseChange c

/-- Inclusion multiplies the class degree by the actual extension degree. -/
theorem ideleClassInclusion_degree :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K,
      (_root_.FunctionField.IdeleClassGroup.degree (k := k) (K := L)
        (ideleClassInclusion k K L c)).toAdd =
        (Module.finrank K L : ℤ) *
          (_root_.FunctionField.IdeleClassGroup.degree (k := k) (K := K) c).toAdd := by
  intro hK hL c
  exact _root_.FunctionField.IdeleClassGroup.degree_baseChange_of_finite c

variable (M : Type) [Field M] [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional L M]

/-- Public norms compose along arbitrary finite towers; the intermediate
function-field presentation is constructed from the original base. -/
theorem ideleClassNorm_trans :
    let presentation := finiteExtensionRatFuncAlgebra k K L
    let _ : Algebra (RatFunc k) L := presentation.val
    have _ : IsScalarTower k (RatFunc k) L := presentation.property.1
    have _ : _root_.FunctionField k L := presentation.property.2
    have _ : FiniteDimensional K M := FiniteDimensional.trans K L M
    let _ : AlgebraicCurve.HasPrincipalDivisors k M :=
      (finiteExtension_isCurveOver k K M).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k M,
      ideleClassNorm k K L (ideleClassNorm k L M c) = ideleClassNorm k K M c := by
  intro presentation aRL hRL hLfield hKMfinite hM c
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.IdeleClassGroup.finiteNorm_trans c

/-- Public inclusions compose along every finite tower, including inseparable
extensions; the intermediate function-field presentation is constructed here. -/
theorem ideleClassInclusion_trans :
    let presentation := finiteExtensionRatFuncAlgebra k K L
    let _ : Algebra (RatFunc k) L := presentation.val
    have _ : IsScalarTower k (RatFunc k) L := presentation.property.1
    have _ : _root_.FunctionField k L := presentation.property.2
    have _ : FiniteDimensional K M := FiniteDimensional.trans K L M
    have _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    have _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    have _ : AlgebraicCurve.HasPrincipalDivisors k M :=
      (finiteExtension_isCurveOver k K M).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K,
      ideleClassInclusion k L M (ideleClassInclusion k K L c) =
        ideleClassInclusion k K M c := by
  intro presentation aRL hRL hLfield hKMfinite hK hL hM c
  exact _root_.FunctionField.IdeleClassGroup.baseChange_trans
    (k := k) (K := K) (L := L) (M := M) c

end ClassFieldTheory.FunctionField
