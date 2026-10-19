/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.HilbertClassField
import Nyll.ClassFieldTheory.Definitions.FunctionField.RayClass
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.Classification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Hilbert norm groups, complete splitting and maximality

The actual selected extension has the prescribed split zero-ray norm group.
Its original places are unramified, and those above the prescribed finite
set have residue degree one. These properties characterize its subfields.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace ClassFieldTheory.FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- The actual Hilbert norm subgroup is the zero-ray subgroup enlarged
by the full local groups at all prescribed splitting places. -/
theorem hilbertClassField_normSubgroup
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    (finiteAbelianNormSubgroup k K (hilbertClassField k K S hS)).val.toSubgroup =
      splitRaySubgroup k K 0 S := by
  intro hK
  exact congrArg
    (fun U : {H : OpenSubgroup (_root_.FunctionField.IdeleClassGroup k K) //
      H.toSubgroup.FiniteIndex} => U.val.toSubgroup)
    (_root_.FunctionField.finiteAbelianFieldNormSubgroupOrderIso_symm_norm k K
      ⟨⟨_root_.FunctionField.RayClass.splitRaySubgroup 0 S,
          _root_.FunctionField.RayClass.isOpen_splitRaySubgroup 0 S⟩,
        _root_.FunctionField.RayClass.finiteIndex_splitRaySubgroup 0 S hS⟩)

/-- The chosen Hilbert field is unramified at every original place and
completely split above every prescribed place. -/
theorem hilbertClassField_spec
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (∀ w : AlgebraicCurve.Place k (hilbertClassField k K S hS).val,
      w.ramificationIndex K = 1) ∧
      (∀ w : AlgebraicCurve.Place k (hilbertClassField k K S hS).val,
        w.restrict K ∈ S → w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ hkKΩ
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.hilbertClassField_spec k K S hS

/-- A finite abelian subextension lies in the Hilbert field exactly when
it is everywhere unramified and completely split at the prescribed places. -/
theorem le_hilbertClassField_iff
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty)
    (E : FiniteAbelianExtension K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    E.val ≤ (hilbertClassField k K S hS).val ↔
      (∀ w : AlgebraicCurve.Place k E.val, w.ramificationIndex K = 1) ∧
      (∀ w : AlgebraicCurve.Place k E.val, w.restrict K ∈ S →
        w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ hkKΩ
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.le_hilbertClassField_iff k K S hS E


/-- The largest everywhere-unramified finite abelian extension in which all
prescribed places split completely exists uniquely in the fixed separable closure. -/
theorem existsUnique_hilbertClassField
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∃! E : FiniteAbelianExtension K, ∀ F : FiniteAbelianExtension K,
      F.val ≤ E.val ↔
        (∀ w : AlgebraicCurve.Place k F.val, w.ramificationIndex K = 1) ∧
        (∀ w : AlgebraicCurve.Place k F.val, w.restrict K ∈ S →
          w.ramificationIndex K = 1 ∧ w.inertiaDeg K = 1) := by
  intro akΩ hkKΩ
  refine ⟨hilbertClassField k K S hS, ?_, ?_⟩
  · intro F
    exact le_hilbertClassField_iff k K S hS F
  · intro E hE
    apply Subtype.ext
    apply le_antisymm
    · have hproperties := (hE E).mp le_rfl
      exact (le_hilbertClassField_iff k K S hS E).mpr hproperties
    · exact (hE (hilbertClassField k K S hS)).mpr (hilbertClassField_spec k K S hS)

end ClassFieldTheory.FunctionField
