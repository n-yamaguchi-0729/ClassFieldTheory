/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Finite abelian reciprocity for function fields

The continuous public Artin map is surjective and its kernel is the actual
all-place idele-class norm image. The quotient isomorphism below evaluates
to this same Artin map on each idele class.
The base function-field hypothesis and finite extension supply all
principal-divisor properties; no presentation of the upper field is required.

These assertions do not include the separate local-global comparison or
the arithmetic Frobenius formula at a general unramified place.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Every automorphism in a finite abelian extension is an Artin value. -/
theorem finiteArtin_surjective : Function.Surjective (finiteArtin k K L) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.abelianFiniteArtin_surjective k K L

/-- The public Artin kernel is the image of the actual idele-class norm. -/
theorem finiteArtin_ker :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    (finiteArtin k K L).toMonoidHom.ker =
      (_root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  intro hK hL
  exact _root_.FunctionField.abelianFiniteArtin_ker k K L

/-- An idele class has trivial Artin value exactly when it is a norm class. -/
theorem finiteArtin_eq_one_iff_exists_norm :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K, finiteArtin k K L c = 1 ↔
      ∃ d : _root_.FunctionField.IdeleClassGroup k L,
        _root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := L) d = c := by
  intro hK hL c
  exact _root_.FunctionField.abelianFiniteArtin_eq_one_iff_mem_norm k K L c

/-- The actual norm quotient is isomorphic to the Galois group through the public Artin map. -/
theorem finiteAbelianGlobalReciprocityQuotient :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    ∃ e : (_root_.FunctionField.IdeleClassGroup k K ⧸
        (_root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
          Gal(L/K),
      ∀ c : _root_.FunctionField.IdeleClassGroup k K,
        e (QuotientGroup.mk c) = finiteArtin k K L c := by
  intro hK hL
  refine ⟨_root_.FunctionField.abelianFiniteNormQuotientEquiv k K L, ?_⟩
  intro c
  rfl

end ClassFieldTheory.FunctionField
