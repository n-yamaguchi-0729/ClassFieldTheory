/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldPresentation
import Nyll.ClassFieldTheory.Algebra.GaloisAbelianization

/-!
# Independence from fixed-field presentation isomorphisms

The norm-quotient transport depends on the base inclusion, while changing
the upper isomorphism changes Galois transport by an inner automorphism.
Thus the resulting reciprocity isomorphism is unchanged.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K L Ω : Type) [Field k] [Finite k] [Field K] [Field L] [Field Ω]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Changing the isomorphisms to the same fixed fields does not change reciprocity. -/
theorem normQuotientEquivOfFixedFieldPresentation_eq
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (eF eF' : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE eE' : L ≃ₐ[K] abstractFixedField K Ω T.field) :
    normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE =
      normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF' eE' := by
  dsimp only [normQuotientEquivOfFixedFieldPresentation,
    IdeleClassGroup.normQuotientCongrOfVerticalFinrankOne]
  congr 1
  rw [← abelianizationCongr_trans, ← abelianizationCongr_trans]
  congr 1
  exact ClassFieldTheory.autCongr_abelianizationCongr_eq eE.symm eE'.symm

end FunctionField
