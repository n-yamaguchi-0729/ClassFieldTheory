/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.ClassField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.Classification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Existence and uniqueness of actual function-field class fields

Every finite-index open subgroup in the usual topology is an actual norm
image. Norms and class fields are inverse and reverse inclusion. All
principal-divisor properties are supplied by the function-field theorem.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- The public subgroup is the image of the actual all-place class norm. -/
theorem finiteAbelianNormSubgroup_eq_norm (E : FiniteAbelianExtension K) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : AlgebraicCurve.HasPrincipalDivisors k E.val :=
      (finiteExtension_isCurveOver k K E.val).toHasPrincipalDivisors
    (finiteAbelianNormSubgroup k K E).val.toSubgroup =
      (_root_.FunctionField.IdeleClassGroup.norm (k := k) (K := K) (L := E.val)).range := by
  intro hK akΩ hkKΩ hE
  rfl

/-- The selected class field has exactly the prescribed actual norm subgroup. -/
theorem classField_normSubgroup (H : OpenFiniteIndexSubgroup k K) :
    finiteAbelianNormSubgroup k K (classField k K H) = H := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.finiteAbelianFieldNormSubgroupOrderIso_symm_norm k K H

/-- The class field of an actual norm subgroup is the original subextension. -/
theorem classField_finiteAbelianNormSubgroup (E : FiniteAbelianExtension K) :
    classField k K (finiteAbelianNormSubgroup k K E) = E :=
  (classFieldCorrespondence k K).symm_apply_apply E

/-- Actual norm inclusion is exactly reverse inclusion of the subextensions. -/
theorem finiteAbelianNormSubgroup_le_iff (E F : FiniteAbelianExtension K) :
    finiteAbelianNormSubgroup k K E ≤ finiteAbelianNormSubgroup k K F ↔ F ≤ E :=
  (classFieldCorrespondence k K).map_rel_iff'

/-- Every ordinary open finite-index subgroup has a unique actual finite
abelian class field, with no extra principal-divisor hypothesis. -/
theorem existsUnique_classField :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    ∀ (H : Subgroup (_root_.FunctionField.IdeleClassGroup k K)),
      IsOpen (H : Set (_root_.FunctionField.IdeleClassGroup k K)) → H.FiniteIndex →
      ∃! E : FiniteAbelianExtension K, (finiteAbelianNormSubgroup k K E).val.toSubgroup = H := by
  intro hK H hH hfinite
  let U : OpenFiniteIndexSubgroup k K := ⟨⟨H, hH⟩, hfinite⟩
  refine ⟨classField k K U, ?_, ?_⟩
  · exact congrArg (fun V : OpenFiniteIndexSubgroup k K => V.val.toSubgroup)
      (classField_normSubgroup k K U)
  · intro E hE
    have hEU : finiteAbelianNormSubgroup k K E = U := by
      apply Subtype.ext
      exact OpenSubgroup.toSubgroup_injective hE
    have hfield := congrArg (classField k K) hEU
    rw [classField_finiteAbelianNormSubgroup] at hfield
    exact hfield

end ClassFieldTheory.FunctionField
