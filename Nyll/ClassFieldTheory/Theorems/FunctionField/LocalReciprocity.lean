/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.LocalArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRestriction
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm

/-!
# The image and norm kernel of local function-field reciprocity

These public statements identify the image with the actual decomposition
subgroup and trivial values with genuine completed field norms.
-/

noncomputable section

open scoped AlgebraicCurve.Place
open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange
open BifibreW2

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The local Artin image is exactly the decomposition subgroup of the chosen place. -/
theorem localArtin_range (w : AlgebraicCurve.Place k L) :
    (localArtin k K L w).toMonoidHom.range =
      _root_.FunctionField.IdeleGroup.decompositionGroup (K := K) w := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.localArtin_range (K := K) w

/-- A local element has trivial Artin value exactly when it is a completed field norm. -/
theorem localArtin_eq_one_iff_exists_norm (w : AlgebraicCurve.Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    localArtin k K L w x = 1 ↔ ∃ y : w.adicCompletionˣ,
      _root_.FunctionField.IdeleGroup.localNorm (K := K) w y = x := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.localArtin_eq_one_iff (K := K) w x

/-- The local Artin kernel is the image of the actual norm on completed units. -/
theorem localArtin_ker (w : AlgebraicCurve.Place k L) :
    (localArtin k K L w).toMonoidHom.ker =
      (_root_.FunctionField.IdeleGroup.localNorm (K := K) w).range := by
  apply Subgroup.ext
  intro x
  exact localArtin_eq_one_iff_exists_norm k K L w x


/-- Norm compatibility of local reciprocity in a finite abelian function-field
tower. The upper function-field presentation is supplied by the given base. -/
theorem localArtin_norm_restrictScalars
    (M : Type) [Field M] [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsAbelianGalois K M] :
    let presentation := finiteExtensionRatFuncAlgebra k K L
    let _ : Algebra (RatFunc k) L := presentation.val
    let _ : IsScalarTower k (RatFunc k) L := presentation.property.1
    let _ : _root_.FunctionField k L := presentation.property.2
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    let _ : IsAbelianGalois L M := IsAbelianGalois.tower_top K L M
    ∀ (u : AlgebraicCurve.Place k M) (x : (u.restrict L).adicCompletionˣ),
      (localArtin k L M u x).restrictScalars K =
        localArtin k K M u
          (_root_.FunctionField.IdeleGroup.localNormOver (u.restrict K) (u.restrict L)
            (restrict_restrict
              (F := K) (E := L) u) x) := by
  intro presentation aRL hkRL hLfield hLMfinite hLMabelian u x
  have hRKL : IsScalarTower (RatFunc k) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  have hM : AlgebraicCurve.HasPrincipalDivisors k M :=
    (finiteExtension_isCurveOver k K M).toHasPrincipalDivisors
  exact _root_.FunctionField.localArtin_norm_restrictScalars (K := K) (L := L) u x


/-- Local reciprocity commutes with restriction to an abelian subextension,
using the same original local element at the restricted base place. -/
theorem localArtin_restrictNormal
    (M : Type) [Field M] [Algebra k M] [Algebra K M] [Algebra L M]
    [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    (u : AlgebraicCurve.Place k M) (x : (u.restrict K).adicCompletionˣ) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    AlgEquiv.restrictNormalHom L (localArtin k K M u x) =
      localArtin k K L (u.restrict L)
        ((restrict_restrict (F := K) (E := L) u).symm ▸ x) := by
  intro hLMfinite
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  have hM : AlgebraicCurve.HasPrincipalDivisors k M :=
    (finiteExtension_isCurveOver k K M).toHasPrincipalDivisors
  exact _root_.FunctionField.localArtin_restrictNormal (K := K) (L := L) u x

end ClassFieldTheory.FunctionField
