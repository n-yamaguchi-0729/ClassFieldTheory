/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormCofinality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SubextensionCorrespondence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormUniqueness
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Class fields for the ordinary idele-class topology

Actual norm cofinality and the finite subextension correspondence give an
exact class field for every ordinary open subgroup of finite index. The
norm map is an order-reversing equivalence, using the existing concrete
finite-abelian intermediate-field type, whose definition needs only a field.
-/

noncomputable section

namespace FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every ordinary open finite-index subgroup is the exact actual norm image
of a finite abelian extension in the fixed separable closure. -/
theorem exists_classField_of_open
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E)
      (_ : IsAbelianGalois K E),
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = H := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  obtain ⟨A, hA, hAN⟩ :=
    exists_finiteAbelian_norm_le_of_open k K (SeparableClosure K) H hH
  have hAabelian : IsAbelianGalois K A := hA
  obtain ⟨E, hEfinite, hEabelian, _, hEnorm⟩ :=
    exists_subextension_norm_eq k K A.toIntermediateField H hAN
  exact ⟨E, hEfinite, hEabelian, hEnorm⟩

/-- The actual norm subgroup, with its proved ordinary openness and finite
index. The finite extension inherits a rational parameter from the base. -/
def finiteAbelianNormOpenSubgroup
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    {H : OpenSubgroup (IdeleClassGroup k K) // H.toSubgroup.FiniteIndex} := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hprincipal : AlgebraicCurve.HasPrincipalDivisors k E.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E.val).toHasPrincipalDivisors
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E.val
  let aRE : Algebra (RatFunc k) E.val := presentation.val
  have hkRE : IsScalarTower k (RatFunc k) E.val := presentation.property.1
  have hfunction : FunctionField k E.val := presentation.property.2
  exact ⟨{ toSubgroup := (IdeleClassGroup.norm (k := k) (K := K) (L := E.val)).range
           isOpen' := IdeleClassGroup.isOpen_norm_range (k := k) (K := K) (L := E.val) },
    IdeleClassGroup.norm_range_finiteIndex (k := k) (K := K) (L := E.val)⟩

/-- Finite abelian subextensions of the fixed separable closure correspond,
with reversed inclusion, to finite-index open subgroups in the ordinary
idele-class topology. The correspondence is the actual class norm. -/
def finiteAbelianFieldNormSubgroupOrderIso :
    ClassFieldTheory.FiniteAbelianLocalExtension K ≃o
      ({H : OpenSubgroup (IdeleClassGroup k K) // H.toSubgroup.FiniteIndex})ᵒᵈ := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let f : ClassFieldTheory.FiniteAbelianLocalExtension K →
      ({H : OpenSubgroup (IdeleClassGroup k K) // H.toSubgroup.FiniteIndex})ᵒᵈ :=
    fun E => OrderDual.toDual (finiteAbelianNormOpenSubgroup k K E)
  have hf : Function.Bijective f := by
    constructor
    · intro E F h
      apply Subtype.ext
      apply (finiteAbelian_norm_range_eq_iff k K E.val F.val).mp
      exact congrArg (fun U => (OrderDual.ofDual U).val.toSubgroup) h
    · intro H
      have hHfinite : (OrderDual.ofDual H).val.toSubgroup.FiniteIndex :=
        (OrderDual.ofDual H).property
      obtain ⟨E, hEfinite, hEabelian, hEnorm⟩ :=
        exists_classField_of_open k K (OrderDual.ofDual H).val.toSubgroup
          (OrderDual.ofDual H).val.isOpen
      refine ⟨⟨E, hEfinite, hEabelian⟩, ?_⟩
      apply Subtype.ext
      apply OpenSubgroup.toSubgroup_injective
      exact hEnorm
  exact { toEquiv := Equiv.ofBijective f hf
          map_rel_iff' := by
            intro E F
            exact finiteAbelian_norm_range_le_iff k K F.val E.val }

/-- The forward classification map is the actual open norm subgroup. -/
theorem finiteAbelianFieldNormSubgroupOrderIso_apply
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    OrderDual.ofDual (finiteAbelianFieldNormSubgroupOrderIso k K E) =
      finiteAbelianNormOpenSubgroup k K E :=
  rfl

/-- The class field selected by the inverse correspondence has exactly the
prescribed ordinary open subgroup as its actual norm image. -/
theorem finiteAbelianFieldNormSubgroupOrderIso_symm_norm
    (H : {H : OpenSubgroup (IdeleClassGroup k K) // H.toSubgroup.FiniteIndex}) :
    finiteAbelianNormOpenSubgroup k K
      ((finiteAbelianFieldNormSubgroupOrderIso k K).symm (OrderDual.toDual H)) = H := by
  exact congrArg OrderDual.ofDual
    ((finiteAbelianFieldNormSubgroupOrderIso k K).apply_symm_apply (OrderDual.toDual H))

end FunctionField
