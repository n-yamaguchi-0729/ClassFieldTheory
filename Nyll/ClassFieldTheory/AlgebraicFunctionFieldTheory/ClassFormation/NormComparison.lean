/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormSummands
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediateTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormProduct

/-!
# The abstract norm is the actual idele-class norm

The fixed-field comparison intertwines norms: the actual product of Galois
conjugates becomes the abstract coset sum. This identifies the norm subgroup
used by abstract reciprocity with the norm of the actual all-place ideles.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open IdeleClassGroup.FiniteExtensionLimit
open scoped BigOperators

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The finite fixed-field equivalences carry the actual class norm to the
abstract relative norm, with its actual Galois quotient indexing. -/
theorem abstractFixedClassEquiv_norm (H J : FiniteAbstractField Gal(Ω/K))
    (hJH : J.field.toSubgroup ≤ H.field.toSubgroup)
    (hnormal : (extensionSubgroup H.field J.field hJH).Normal)
    [Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field hJH)] :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω J.field) :=
      abstractFixedField_finiteDimensional K Ω J.field J.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      abstractRelativeFixedField_isGalois K Ω H.field J.field hJH hnormal
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω J.field)),
      abstractFixedClassEquiv k K Ω H.field H.finite
          (Additive.ofMul (IdeleClassGroup.norm (k := k)
            (K := abstractFixedField K Ω H.field) (L := abstractFixedField K Ω J.field) c.toMul)) =
        relativeNorm (ideleClassRepresentation k K Ω) H.field J.field hJH
          (abstractFixedClassEquiv k K Ω J.field J.finite c) := by
  intro hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEgal c
  let F := abstractFixedField K Ω H.field
  let E := abstractFixedField K Ω J.field
  apply Subtype.ext
  rw [abstractFixedClassEquiv_coe]
  have hN := abstractFixedClassEquiv_relativeNormValue k K Ω
    H.field J.field hJH hnormal J.finite c
  apply Eq.trans _ hN.symm
  apply congrArg Additive.ofMul
  calc
    ofIntermediate (k := k) F (IdeleClassGroup.norm (k := k) (K := F) (L := E) c.toMul) =
        ofIntermediate (k := k) E (IdeleClassGroup.baseChange (k := k) (K := F) (L := E)
          (IdeleClassGroup.norm (k := k) (K := F) (L := E) c.toMul)) :=
      (ofIntermediate_baseChange F E (abstractFixedField_le K Ω hJH) _).symm
    _ = _ := congrArg (ofIntermediate (k := k) E)
      (IdeleClassGroup.baseChange_norm_eq_prod_algAut (k := k) (K := F) (L := E) c.toMul)

end FunctionField
