/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Separable
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction

/-!
# Local norm reciprocity in a finite separable square

The base extension need not be normal. Apply the existing local reciprocity
square to the actual completions and compare its action on the original
upper field. Every completed scalar tower comes from the same completion maps.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k K F L M : Type} [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k F M] [IsScalarTower k L M]
    [IsScalarTower K F M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- Local norm reciprocity for an arbitrary finite separable base change
and a compatible square of finite abelian upper extensions. -/
theorem localArtin_norm_restrictNormal (u : Place k M) :
    let _ : FiniteDimensional K M := FiniteDimensional.trans K F M
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    ∀ x : (u.restrict F).adicCompletionˣ,
      AlgEquiv.restrictNormalHom L ((localArtin (K := F) u x).restrictScalars K) =
        localArtin (K := K) (u.restrict L)
          (IdeleGroup.localNormOver ((u.restrict L).restrict K) (u.restrict F)
            ((restrict_restrict (F := K) (E := F) u).trans
              (restrict_restrict (F := K) (E := L) u).symm) x) := by
  intro hKMfinite hLMfinite x
  let v : Place k K := (u.restrict L).restrict K
  let w : Place k F := u.restrict F
  let z : Place k L := u.restrict L
  have hw : w.restrict K = v :=
    (restrict_restrict (F := K) (E := F) u).trans
      (restrict_restrict (F := K) (E := L) u).symm
  have hu : u.restrict K = v :=
    (restrict_restrict (F := K) (E := L) u).symm
  let avw : Algebra v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionMapOver v w hw).toAlgebra
  let avu : Algebra v.adicCompletion u.adicCompletion :=
    (IdeleGroup.completionMapOver v u hu).toAlgebra
  let rv : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  let rw' : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have hvlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hwlocal : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  have hvwfinite : FiniteDimensional v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteSeparableOver v w hw).1
  have hvwseparable : Algebra.IsSeparable v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteSeparableOver v w hw).2
  have hvwextension : (ValuativeRel.valuation v.adicCompletion).HasExtension
      (ValuativeRel.valuation w.adicCompletion) :=
    IdeleGroup.completionCanonical_hasExtension_over v w hw
  have hvwu : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (IdeleGroup.completionMapOver_trans v w u hw rfl hu)).symm)
  have hvzu : IsScalarTower v.adicCompletion z.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (IdeleGroup.completionMapOver_trans v z u rfl rfl hu)).symm)
  let n : v.adicCompletionˣ := IdeleGroup.localNormOver v w hw x
  have hn : LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion x⁻¹ = n⁻¹ := by
    rw [map_inv]
    exact congrArg Inv.inv (IdeleGroup.localNormOver_eq_norm v w hw x).symm
  have hlocal := DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction
      v.adicCompletion w.adicCompletion z.adicCompletion u.adicCompletion) x⁻¹
  change AlgEquiv.restrictNormalHom z.adicCompletion
      ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
        w.adicCompletion u.adicCompletion x⁻¹).restrictScalars v.adicCompletion) =
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
      v.adicCompletion z.adicCompletion
        (LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion x⁻¹) at hlocal
  rw [hn] at hlocal
  apply AlgEquiv.ext
  intro y
  apply (algebraMap L M).injective
  apply (algebraMap M u.adicCompletion).injective
  have hupper := localArtin_completion_apply (K := F) u x (algebraMap L M y)
  have hlower := localArtin_completion_apply (K := K) z n y
  dsimp only at hupper hlower
  have hglobal := AlgEquiv.restrictNormal_commutes
    ((localArtin (K := F) u x).restrictScalars K) L y
  have hcompleted := AlgEquiv.restrictNormal_commutes
    ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
      w.adicCompletion u.adicCompletion x⁻¹).restrictScalars v.adicCompletion)
    z.adicCompletion (algebraMap L z.adicCompletion y)
  have heval := congrArg
    (fun σ : Gal(z.adicCompletion/v.adicCompletion) =>
      algebraMap z.adicCompletion u.adicCompletion
        (σ (algebraMap L z.adicCompletion y))) hlocal
  have hembed (t : L) :
      algebraMap z.adicCompletion u.adicCompletion (algebraMap L z.adicCompletion t) =
        algebraMap M u.adicCompletion (algebraMap L M t) :=
    IdeleGroup.completionMapOver_algebraMap z u rfl t
  calc
    algebraMap M u.adicCompletion (algebraMap L M
        ((AlgEquiv.restrictNormalHom L ((localArtin (K := F) u x).restrictScalars K)) y)) =
        algebraMap M u.adicCompletion (localArtin (K := F) u x (algebraMap L M y)) :=
      congrArg (algebraMap M u.adicCompletion) hglobal
    _ = LocalClassFieldTheory.abelianLocalArtinMonoidHom
        w.adicCompletion u.adicCompletion x⁻¹
          (algebraMap M u.adicCompletion (algebraMap L M y)) := hupper.symm
    _ = LocalClassFieldTheory.abelianLocalArtinMonoidHom
        w.adicCompletion u.adicCompletion x⁻¹
          (algebraMap z.adicCompletion u.adicCompletion (algebraMap L z.adicCompletion y)) :=
      congrArg (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        w.adicCompletion u.adicCompletion x⁻¹) (hembed y).symm
    _ = algebraMap z.adicCompletion u.adicCompletion
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          v.adicCompletion z.adicCompletion n⁻¹ (algebraMap L z.adicCompletion y)) :=
      hcompleted.symm.trans heval
    _ = algebraMap z.adicCompletion u.adicCompletion
        (algebraMap L z.adicCompletion (localArtin (K := K) z n y)) :=
      congrArg (algebraMap z.adicCompletion u.adicCompletion) hlower
    _ = algebraMap M u.adicCompletion
        (algebraMap L M (localArtin (K := K) z n y)) :=
      hembed (localArtin (K := K) z n y)

end FunctionField
