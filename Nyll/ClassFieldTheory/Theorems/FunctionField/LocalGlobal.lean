/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.Definitions.FunctionField.Norm
import Nyll.ClassFieldTheory.Definitions.FunctionField.LocalArtin
import Nyll.ClassFieldTheory.Definitions.FunctionField.Frobenius
import Nyll.ClassFieldTheory.Theorems.FunctionField.LocalReciprocity
import Nyll.ClassFieldTheory.Theorems.FunctionField.Frobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalDecomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic

/-!
# Global reciprocity at the actual places

The public global symbol agrees with the public local symbol. Its images
detect decomposition, residue inertia and complete splitting. At an
unramified place it is the local-order power of arithmetic Frobenius.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The public finite Artin symbol restricts to actual local reciprocity. -/
theorem localArtin_eq_finiteArtin_placeIdele
    (w : AlgebraicCurve.Place k L) (x : (w.restrict K).adicCompletionˣ) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    localArtin k K L w x = finiteArtin k K L
      (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
        (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x)) := by
  intro hK
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.localArtin_eq_abelianFiniteArtin_placeIdele k K L w x

/-- The image of the whole local group is the actual decomposition subgroup. -/
theorem finiteArtin_placeIdele_range (w : AlgebraicCurve.Place k L) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    ((finiteArtin k K L).toMonoidHom.comp
      ((_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)).comp
        (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K)))).range =
      _root_.FunctionField.IdeleGroup.decompositionGroup (K := K) w := by
  intro hK
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.abelianFiniteArtin_placeIdele_range (K := K) w

/-- Local units have image equal to the kernel of the actual residue action,
included in the global Galois group. -/
theorem finiteArtin_placeIdele_units (w : AlgebraicCurve.Place k L) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    (_root_.FunctionField.RayClass.localHigherUnitGroup (w.restrict K) 0).map
      ((finiteArtin k K L).toMonoidHom.comp
        ((_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)).comp
          (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K)))) =
      (_root_.FunctionField.IdeleGroup.decompositionResidueAut (K := K) w).ker.map
        (_root_.FunctionField.IdeleGroup.decompositionGroup (K := K) w).subtype := by
  intro hK
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfinite : _root_.FunctionField k L := presentation.property.2
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.abelianFiniteArtin_placeIdele_units (K := K) w

/-- A place splits completely exactly when global reciprocity kills its
whole local multiplicative group. -/
theorem finiteArtin_placeIdele_trivial_iff_completelySplit (w : AlgebraicCurve.Place k L) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    (∀ x : (w.restrict K).adicCompletionˣ,
      finiteArtin k K L (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
        (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x)) = 1) ↔
      w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1 := by
  intro hK
  have hL : AlgebraicCurve.HasPrincipalDivisors k L :=
    (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
  exact _root_.FunctionField.abelianFiniteArtin_placeIdele_trivial_iff_completelySplit (K := K) w

/-- The global symbol at an unramified place is the local-order power of
the actual arithmetic Frobenius. -/
theorem finiteArtin_placeIdele_eq_arithmeticFrobenius_zpow
    (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    finiteArtin k K L (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
      (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x)) =
      (arithmeticFrobenius k K L w he).val ^
        (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  intro hK
  have hlocal := localArtin_eq_finiteArtin_placeIdele k K L w x
  dsimp only at hlocal
  rw [← hlocal]
  exact localArtin_eq_arithmeticFrobenius_zpow k K L w he x

/-- A uniformizer has global Artin value equal to arithmetic Frobenius. -/
theorem finiteArtin_uniformizer
    (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    finiteArtin k K L (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
      (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x)) =
      (arithmeticFrobenius k K L w he).val := by
  intro hK
  have hpower := finiteArtin_placeIdele_eq_arithmeticFrobenius_zpow k K L w he x
  dsimp only at hpower
  rw [hpower, hx, zpow_one]

/-- The global symbol of an unramified uniformizer has order equal to the
actual residue degree. -/
theorem orderOf_finiteArtin_uniformizer
    (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    orderOf (finiteArtin k K L
      (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
        (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x))) = w.inertiaDeg K := by
  intro hK
  have huniformizer := finiteArtin_uniformizer k K L w he x hx
  dsimp only at huniformizer
  rw [huniformizer]
  exact (orderOf_injective
    (_root_.FunctionField.IdeleGroup.decompositionGroup (K := K) w).subtype
      Subtype.val_injective (arithmeticFrobenius k K L w he)).trans
    (orderOf_arithmeticFrobenius k K L w he)

/-- At an unramified place, triviality of the global uniformizer symbol
is equivalent to complete splitting. -/
theorem finiteArtin_uniformizer_eq_one_iff
    (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    finiteArtin k K L
        (_root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
          (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x)) = 1 ↔
      w.inertiaDeg K = 1 := by
  intro hK
  have horder := orderOf_finiteArtin_uniformizer k K L w he x hx
  dsimp only at horder
  rw [← orderOf_eq_one_iff, horder]

/-- A one-place idele class at an unramified place is a global norm
precisely when the local order is divisible by the residue degree. -/
theorem placeIdele_mem_norm_iff_inertiaDeg_dvd
    (w : AlgebraicCurve.Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : AlgebraicCurve.HasPrincipalDivisors k L :=
      (finiteExtension_isCurveOver k K L).toHasPrincipalDivisors
    _root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
        (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x) ∈
      (ideleClassNorm k K L).toMonoidHom.range ↔
        (w.inertiaDeg K : ℤ) ∣
          (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  intro hK hL
  let presentation := finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfunctionL : _root_.FunctionField k L := presentation.property.2
  change _root_.FunctionField.IdeleClassGroup.mk (k := k) (K := K)
      (_root_.FunctionField.IdeleGroup.placeIdele (w.restrict K) x) ∈
    (_root_.FunctionField.IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)).range ↔
      (w.inertiaDeg K : ℤ) ∣
        (_root_.FunctionField.IdeleGroup.localOrder (w.restrict K) x).toAdd
  rw [_root_.FunctionField.IdeleClassGroup.finiteNorm_eq_norm]
  exact _root_.FunctionField.placeIdele_mem_norm_range_iff_inertiaDeg_dvd w he x

end ClassFieldTheory.FunctionField
