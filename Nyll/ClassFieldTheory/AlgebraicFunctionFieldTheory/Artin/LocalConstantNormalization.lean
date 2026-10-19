/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalValuationNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization

/-!
# Arithmetic normalization on actual unramified completions

The function-field local symbol sends order-one elements to arithmetic
Frobenius. All local-field, valuative-extension and unramified inputs come
from the actual completions and the original place's ramification index.
The sign comparison accounts for the inverse-standard valuation used by
the common local class-field construction.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place ValuativeRel

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- At every unramified place, the completed local symbol is arithmetic
Frobenius raised to the usual additive order of its input. -/
theorem localDecompositionArtin_completion_eq_frobenius_zpow
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
    let _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    let _ : IsNonarchimedeanLocalField w.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField w
    let _ := IdeleGroup.completionCanonical_hasExtension (K := K) w
    let _ : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
        w.adicCompletion := IdeleGroup.completionCanonical_isIntegralClosure (K := K) w
    let _ : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] := by
      have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
        IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
          (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
      exact Module.IsNoetherian.finite _ _
    let _ := IdeleGroup.completionCanonical_isUnramified (K := K) w he
    IdeleGroup.decompositionCompletionEquiv (K := K) w
        (localDecompositionArtin (K := K) w x) =
      LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation
          (w.restrict K).adicCompletion w.adicCompletion ^
        (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  intro hbaseRelation hextensionRelation hbaseLocal hextensionLocal
    hextension hclosure hfinite hunramified
  have hx : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
      (w.restrict K).adicCompletion (Additive.ofMul x⁻¹) =
        (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_inv,
      placeCompletion_valuationMap_eq_neg_localOrder, neg_neg]
  change IdeleGroup.decompositionCompletionEquiv (K := K) w
      ((IdeleGroup.decompositionCompletionEquiv (K := K) w).symm
        (LocalClassFieldTheory.abelianLocalArtinMap
          (w.restrict K).adicCompletion w.adicCompletion x⁻¹)) = _
  rw [MulEquiv.apply_symm_apply,
    ClassFieldTheory.finiteAbelianLocalArtinMap_eq_frobenius_zpow, hx]

end FunctionField
