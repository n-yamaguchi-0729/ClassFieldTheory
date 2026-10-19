/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom

/-!
# Continuous finite abelian reciprocity on actual fixed fields

Actual norm openness proves continuity for the usual idele-class topology.
The quotient isomorphism has the actual finite relative Galois group as target.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The finite abelian symbol has exactly the actual norm subgroup as its kernel. -/
theorem abelianFixedFieldArtin_ker (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω L.field) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    (abelianFixedFieldArtin k K Ω H L).ker =
      (IdeleClassGroup.norm (k := k)
        (K := abstractFixedField K Ω H.field) (L := abstractFixedField K Ω L.field)).range := by
  intro hrelfinite hupper hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEgal
  apply Subgroup.ext
  intro c
  exact (abelianFixedFieldArtin_eq_one_iff k K Ω H L c).trans
    (fixedFieldArtin_eq_one_iff_mem_norm k K Ω H L.toFiniteGaloisExtension c)

/-- The finite abelian symbol is continuous for the usual idele-class and Krull topologies. -/
theorem continuous_abelianFixedFieldArtin (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω L.field) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    Continuous (abelianFixedFieldArtin k K Ω H L) := by
  intro hrelfinite hupper hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEgal
  apply ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete
  rw [abelianFixedFieldArtin_ker]
  exact IdeleClassGroup.isOpen_norm_range

/-- Actual norm classes are canonically the actual finite abelian Galois group. -/
def abelianFixedFieldNormQuotientEquiv (H : FiniteAbstractField Gal(Ω/K))
    (L : FiniteAbelianSubextension H.field) :
    let _ := L.finite
    let hupper : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/K)) L.field (le_baseField L.field)) :=
      FiniteGaloisSubextension.finite_extension_trans L.below (le_baseField H.field)
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω L.field) :=
      abstractFixedField_finiteDimensional K Ω L.field hupper
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω L.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractFixedField K Ω L.field) :=
      abstractRelativeFixedField_isGalois K Ω H.field L.field L.below L.normal
    (IdeleClassGroup k (abstractFixedField K Ω H.field) ⧸
      (IdeleClassGroup.norm (k := k)
        (K := abstractFixedField K Ω H.field) (L := abstractFixedField K Ω L.field)).range) ≃*
      Gal((abstractFixedField K Ω L.field)/(abstractFixedField K Ω H.field)) := by
  intro hrelfinite hupper hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEgal
  exact (QuotientGroup.quotientMulEquivOfEq (abelianFixedFieldArtin_ker k K Ω H L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (abelianFixedFieldArtin k K Ω H L)
      (abelianFixedFieldArtin_surjective k K Ω H L))

end FunctionField
