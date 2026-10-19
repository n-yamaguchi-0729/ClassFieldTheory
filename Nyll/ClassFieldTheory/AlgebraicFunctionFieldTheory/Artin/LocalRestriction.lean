/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2Over
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality

/-!
# Restricting local Artin automorphisms in a function-field tower

The existing restriction law for local reciprocity is applied to the actual
tower of completed fields. Evaluation on the embedded original field then
identifies the restrictions of the actual decomposition automorphisms.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

section CompletionTransport

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

private theorem completionIsAbelianGalois_over
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionMapOver v w hw).toAlgebra
    IsAbelianGalois v.adicCompletion w.adicCompletion := by
  have h : IsAbelianGalois (w.restrict K).adicCompletion w.adicCompletion :=
    inferInstance
  subst v
  exact h

variable [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

private theorem localArtin_completion_apply_over
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (x : v.adicCompletionˣ) (y : L) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionMapOver v w hw).toAlgebra
    let _ : FiniteDimensional v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionFiniteGaloisOver v w hw).1
    let _ : IsAbelianGalois v.adicCompletion w.adicCompletion :=
      completionIsAbelianGalois_over v w hw
    let _ : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    let _ : IsNonarchimedeanLocalField v.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField v
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
        v.adicCompletion w.adicCompletion x⁻¹
        (algebraMap L w.adicCompletion y) =
      algebraMap L w.adicCompletion (localArtin (K := K) w (hw.symm ▸ x) y) := by
  subst v
  exact localArtin_completion_apply w x y

end CompletionTransport

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k K L M : Type} [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- Restriction of the local Artin automorphism to a finite abelian
subextension is its own local Artin automorphism at the restricted place. -/
theorem localArtin_restrictNormal (u : Place k M)
    (x : (u.restrict K).adicCompletionˣ) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    AlgEquiv.restrictNormalHom L (localArtin (K := K) u x) =
      localArtin (K := K) (u.restrict L)
        ((restrict_restrict (F := K) (E := L) u).symm ▸ x) := by
  intro hLMfinite
  let v : Place k K := u.restrict K
  let w : Place k L := u.restrict L
  have hw : w.restrict K = v := restrict_restrict (F := K) (E := L) u
  have hLMgalois : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let avw : Algebra v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionMapOver v w hw).toAlgebra
  have hvwfinite : FiniteDimensional v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteGaloisOver v w hw).1
  have hvwabelian : IsAbelianGalois v.adicCompletion w.adicCompletion :=
    completionIsAbelianGalois_over v w hw
  let rv : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have hvlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hvwu : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (IdeleGroup.completionMapOver_trans v w u hw rfl rfl)).symm)
  have hlocal := DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower
      v.adicCompletion w.adicCompletion u.adicCompletion) x⁻¹
  apply AlgEquiv.ext
  intro y
  apply (algebraMap L w.adicCompletion).injective
  apply (algebraMap w.adicCompletion u.adicCompletion).injective
  have hcomm := AlgEquiv.restrictNormal_commutes
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom
      v.adicCompletion u.adicCompletion x⁻¹) w.adicCompletion
    (algebraMap L w.adicCompletion y)
  have hglobal := AlgEquiv.restrictNormal_commutes
    (localArtin (K := K) u x) L y
  have hupper := localArtin_completion_apply (K := K) u x (algebraMap L M y)
  have hlower := localArtin_completion_apply_over v w hw x y
  have hrestriction := congrArg
    (fun σ : Gal(w.adicCompletion/v.adicCompletion) =>
      algebraMap w.adicCompletion u.adicCompletion
        (σ (algebraMap L w.adicCompletion y))) hlocal
  change IdeleGroup.completionMapOver w u rfl
      (algebraMap L w.adicCompletion ((localArtin (K := K) u x).restrictNormal L y)) =
    IdeleGroup.completionMapOver w u rfl
      (algebraMap L w.adicCompletion (localArtin (K := K) w (hw.symm ▸ x) y))
  rw [IdeleGroup.completionMapOver_algebraMap, hglobal]
  rw [← hupper]
  change algebraMap w.adicCompletion u.adicCompletion
      (((LocalClassFieldTheory.abelianLocalArtinMonoidHom
        v.adicCompletion u.adicCompletion x⁻¹).restrictNormal w.adicCompletion)
        (algebraMap L w.adicCompletion y)) =
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
      v.adicCompletion u.adicCompletion x⁻¹
      (IdeleGroup.completionMapOver w u rfl (algebraMap L w.adicCompletion y)) at hcomm
  rw [IdeleGroup.completionMapOver_algebraMap] at hcomm
  exact hcomm.symm.trans (hrestriction.trans
    (congrArg (algebraMap w.adicCompletion u.adicCompletion) hlower))

end FunctionField
