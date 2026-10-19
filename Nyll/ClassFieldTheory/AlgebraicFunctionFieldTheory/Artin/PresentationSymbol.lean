/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldPresentation

/-!
# Values of reciprocity under a fixed-field presentation

The transported norm-quotient isomorphism evaluates on an idele class by
base change, the actual fixed-field Artin map, and Galois transport.
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

/-- Evaluation of reciprocity transported through two field isomorphisms. -/
theorem normQuotientEquivOfFixedFieldPresentation_mk
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (eF : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE : L ≃ₐ[K] abstractFixedField K Ω T.field) :
    let hKFfinite : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : IsGalois K (abstractFixedField K Ω H.field) := IsGalois.of_algEquiv eF
    let aFE : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω T.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    let hKFE : IsScalarTower K (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let hFdegree : Module.finrank K (abstractFixedField K Ω H.field) = 1 := by
      rw [← eF.toLinearEquiv.finrank_eq, Module.finrank_self]
    ∀ c : IdeleClassGroup k K,
      normQuotientEquivOfFixedFieldPresentation k K L Ω H T eF eE (QuotientGroup.mk c) =
        ((ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
            (K := K) (F := abstractFixedField K Ω H.field)
            (E := abstractFixedField K Ω T.field) hFdegree).trans
          (AlgEquiv.autCongr eE).symm).abelianizationCongr
          (fixedFieldArtin k K Ω H T
            (IdeleClassGroup.baseChange (k := k) (K := K)
              (L := abstractFixedField K Ω H.field) c)) := by
  intro hKFfinite hKFgal aFE hKFE hFdegree c
  let F := abstractFixedField K Ω H.field
  let E := abstractFixedField K Ω T.field
  have hKEfinite : FiniteDimensional K E := eE.toLinearEquiv.finiteDimensional
  have hKEgal : IsGalois K E := IsGalois.of_algEquiv eE
  have hkFE : IsScalarTower k F E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFEfinite : FiniteDimensional F E := FiniteDimensional.right K F E
  have hFEgal : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
  let aLE : Algebra L E := eE.toAlgHom.toAlgebra
  have hKLE : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq (fun x => (eE.commutes x).symm)
  have hkLE : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply k K E, IsScalarTower.algebraMap_apply k K L,
      ← IsScalarTower.algebraMap_apply K L E])
  let eL : L ≃ₐ[L] E := { eE.toRingEquiv with commutes' := fun _ => rfl }
  have hLEfinite : FiniteDimensional L E := eL.toLinearEquiv.finiteDimensional
  have hLEgal : IsGalois L E := IsGalois.of_algEquiv eL
  have hEdegree : Module.finrank L E = 1 :=
    Module.finrank_of_bijective_algebraMap eE.bijective
  let eN := IdeleClassGroup.normQuotientCongrOfVerticalFinrankOne
    (k := k) (K := K) (L := L) (F := F) (E := E) hFdegree hEdegree
  let eG : Gal(E/F) ≃* Gal(L/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
      (K := K) (F := F) (E := E) hFdegree).trans (AlgEquiv.autCongr eE).symm
  change eG.abelianizationCongr
    (fixedFieldNormQuotientEquiv k K Ω H T (eN (QuotientGroup.mk c))) = _
  have hN := IdeleClassGroup.normQuotientCongrOfVerticalFinrankOne_mk
    (k := k) (K := K) (L := L) (F := F) (E := E) hFdegree hEdegree c
  have hsymbol := fixedFieldNormQuotientEquiv_mk k K Ω H T
    (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c)
  exact congrArg eG.abelianizationCongr
    ((congrArg (fixedFieldNormQuotientEquiv k K Ω H T) hN).trans hsymbol)

end FunctionField
