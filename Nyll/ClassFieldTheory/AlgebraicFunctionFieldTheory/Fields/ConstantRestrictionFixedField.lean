/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Mathlib.GroupTheory.Index

/-!
# Fixed constants and the image of absolute constant restriction

The fixed field of the restriction image is the actual algebraic constant
field of the original fixed field. Consequently its degree equals the index
of that image, with no normality assumption on the subgroup.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- Fixed elements in the constant closure are precisely the algebraic
constants in the original fixed field. -/
def constantRestrictionFixedFieldEquiv (H : Subgroup Gal(Ω/K)) :
    IntermediateField.fixedField (H.map (absoluteConstantRestriction k K Ω).toMonoidHom) ≃ₐ[k]
      algebraicClosure k (IntermediateField.fixedField H) := by
  let C := separableClosure k Ω
  let E := IntermediateField.fixedField H
  have hkEΩ : IsScalarTower k E Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let F := IntermediateField.fixedField
    (H.map (absoluteConstantRestriction k K Ω).toMonoidHom)
  let f : F →ₐ[k] E :=
    { toFun := fun x => ⟨(x.1 : Ω), by
        apply (IntermediateField.mem_fixedField_iff _ _).mpr
        intro σ hσ
        have hx := (IntermediateField.mem_fixedField_iff _ _).mp x.2
          (absoluteConstantRestriction k K Ω σ) ⟨σ, hσ, rfl⟩
        exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) C x.1).symm.trans
          (congrArg Subtype.val hx)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let g : F →ₐ[k] algebraicClosure k E :=
    { toFun := fun x => ⟨f x, mem_algebraicClosure_iff.mpr
        ((Algebra.IsAlgebraic.isAlgebraic x).algHom f)⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y)
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun x y => Subtype.ext (f.map_add x y)
      commutes' := fun x => Subtype.ext (f.commutes x) }
  apply AlgEquiv.ofBijective g
  refine ⟨g.injective, ?_⟩
  intro y
  have hysep : IsSeparable k (y : E) :=
    PerfectField.separable_of_irreducible
      (minpoly.irreducible (mem_algebraicClosure_iff'.mp y.2))
  let i : E →ₐ[k] Ω := IsScalarTower.toAlgHom k E Ω
  let c : C := ⟨i y.1, mem_separableClosure_iff.mpr (IsSeparable.map i i.injective hysep)⟩
  have hc : c ∈ F := by
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    rintro τ ⟨σ, hσ, rfl⟩
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) C c).trans
      ((IntermediateField.mem_fixedField_iff _ _).mp y.1.2 σ hσ)
  exact ⟨⟨c, hc⟩, rfl⟩

variable [IsGalois K Ω]

omit [Finite k] in
/-- The image of a closed subgroup under constant restriction is closed. -/
theorem constantRestriction_isClosed_map (H : ClosedSubgroup Gal(Ω/K)) :
    IsClosed ((H.toSubgroup.map (absoluteConstantRestriction k K Ω).toMonoidHom) :
      Set Gal(separableClosure k Ω / k)) := by
  change IsClosed ((absoluteConstantRestriction k K Ω) '' (H : Set Gal(Ω/K)))
  exact (absoluteConstantRestriction k K Ω).continuous_toFun.isClosedMap _ H.isClosed'

/-- Constant-field degree is the actual index of the restriction image. -/
theorem finrank_constants_eq_constantRestriction_index (H : ClosedSubgroup Gal(Ω/K)) :
    Module.finrank k (algebraicClosure k (IntermediateField.fixedField H.toSubgroup)) =
      (H.toSubgroup.map (absoluteConstantRestriction k K Ω).toMonoidHom).index := by
  let J : ClosedSubgroup Gal(separableClosure k Ω / k) :=
    ⟨H.toSubgroup.map (absoluteConstantRestriction k K Ω).toMonoidHom,
      constantRestriction_isClosed_map k K Ω H⟩
  rw [← (constantRestrictionFixedFieldEquiv k K Ω H.toSubgroup).toLinearEquiv.finrank_eq]
  change Module.finrank k (IntermediateField.fixedField J.toSubgroup) = J.toSubgroup.index
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    InfiniteGalois.fixingSubgroup_fixedField J]

/-- Passing to arithmetic Frobenius coordinates preserves this index. -/
theorem finrank_constants_eq_absoluteConstantDegree_index (H : ClosedSubgroup Gal(Ω/K)) :
    Module.finrank k (algebraicClosure k (IntermediateField.fixedField H.toSubgroup)) =
      (H.toSubgroup.map (absoluteConstantDegree k K Ω).toMonoidHom).index := by
  let : Fintype k := Fintype.ofFinite k
  have : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k
  have : PerfectField (separableClosure k Ω) := Algebra.IsAlgebraic.perfectField k
  rw [finrank_constants_eq_constantRestriction_index]
  change _ = (H.toSubgroup.map
    (((LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn k
      (separableClosure k Ω)).symm.toMulEquiv.toMonoidHom).comp
        (absoluteConstantRestriction k K Ω).toMonoidHom)).index
  rw [← Subgroup.map_map]
  exact (Subgroup.index_map_of_bijective
    (LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn k
      (separableClosure k Ω)).symm.bijective _).symm

end FunctionField
