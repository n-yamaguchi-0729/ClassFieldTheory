/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor

/-!
# Local conductor and actual ramification at a function-field place

The existing completed local conductor vanishes exactly when the original
place has ramification index one. The canonical completion preserves the
ramification index, so no local-global Artin comparison is needed here.
-/

noncomputable section

open scoped AlgebraicCurve.Place ValuativeRel

namespace FunctionField

open AlgebraicCurve

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual completed local conductor is zero exactly at an unramified
original place. The upper function-field presentation is supplied internally. -/
theorem localConductorExponent_eq_zero_iff_ramificationIndex_eq_one (w : Place k L) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    have _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    LocalClassFieldTheory.localConductorExponent
      (w.restrict K).adicCompletion w.adicCompletion = 0 ↔ w.ramificationIndex K = 1 := by
  intro hbaseRelation hbaseLocal
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfunctionL : FunctionField k L := presentation.property.2
  let hextensionRelation : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have hextensionLocal : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  have hextension : (ValuativeRel.valuation (w.restrict K).adicCompletion).HasExtension
      (ValuativeRel.valuation w.adicCompletion) :=
    IdeleGroup.completionCanonical_hasExtension (K := K) w
  have hclosure : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
      w.adicCompletion := IdeleGroup.completionCanonical_isIntegralClosure (K := K) w
  have hnoetherian : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
      (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
  have hfinite : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    Module.IsNoetherian.finite _ _
  have hunramified :=
    LocalClassFieldTheory.isUnramifiedValuedExtension_iff_localConductorExponent_eq_zero
      (w.restrict K).adicCompletion w.adicCompletion
  constructor
  · intro hzero
    have hu := hunramified.mpr hzero
    exact (IdeleGroup.completionCanonical_ramificationIdx (K := K) w).symm.trans
      hu.maximalIdeal_ramificationIdx_eq_one
  · intro he
    exact hunramified.mp (IdeleGroup.completionCanonical_isUnramified (K := K) w he)

end FunctionField
