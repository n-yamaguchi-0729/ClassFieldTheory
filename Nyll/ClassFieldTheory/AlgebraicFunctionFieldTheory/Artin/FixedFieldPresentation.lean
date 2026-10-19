/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormIsomorphism
import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne

/-!
# Reciprocity under a fixed-field presentation

Two explicit algebra equivalences transport actual norm quotients and
relative Galois groups. The actual norm tower identities prove compatibility
of these presentation changes with reciprocity's norm kernel.
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

/-- Transport fixed-field reciprocity through explicit isomorphisms of both fields. -/
def normQuotientEquivOfFixedFieldPresentation
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (eF : K ≃ₐ[K] abstractFixedField K Ω H.field)
    (eE : L ≃ₐ[K] abstractFixedField K Ω T.field) :
    (IdeleClassGroup k K ⧸ (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range) ≃*
      Abelianization Gal(L/K) := by
  let F := abstractFixedField K Ω H.field
  let E := abstractFixedField K Ω T.field
  have hKFfinite : FiniteDimensional K F := eF.toLinearEquiv.finiteDimensional
  have hKEfinite : FiniteDimensional K E := eE.toLinearEquiv.finiteDimensional
  have hKFgal : IsGalois K F := IsGalois.of_algEquiv eF
  have hKEgal : IsGalois K E := IsGalois.of_algEquiv eE
  have hFdegree : Module.finrank K F = 1 := by
    rw [← eF.toLinearEquiv.finrank_eq, Module.finrank_self]
  let aFE : Algebra F E :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
  have hKFE : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkFE : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
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
  have hEdegree : Module.finrank L E = 1 := Module.finrank_of_bijective_algebraMap eE.bijective
  let eG : Gal(E/F) ≃* Gal(L/K) :=
    (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
      (K := K) (F := F) (E := E) hFdegree).trans
      (AlgEquiv.autCongr eE).symm
  exact ((IdeleClassGroup.normQuotientCongrOfVerticalFinrankOne
      (k := k) (K := K) (L := L) (F := F) (E := E) hFdegree hEdegree).trans
    (fixedFieldNormQuotientEquiv k K Ω H T)).trans eG.abelianizationCongr


end FunctionField
