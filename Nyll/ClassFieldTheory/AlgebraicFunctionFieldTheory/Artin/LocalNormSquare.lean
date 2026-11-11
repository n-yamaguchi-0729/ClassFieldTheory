/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Separable
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Local norm reciprocity in a finite separable square

The base extension need not be normal. Apply the existing local reciprocity
square to the actual completions and compare its action on the original
upper field. Every completed scalar tower comes from the same completion maps.
-/

@[expose] public section

universe u v w s t

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

private theorem completedNorm_commutes
    (A : Type u) (B : Type v) (C : Type w) (D : Type s)
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Field C] [Field D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    [FiniteDimensional A B] [Algebra.IsSeparable A B]
    [Valuation.HasExtension (ValuativeRel.valuation A) (ValuativeRel.valuation B)]
    [FiniteDimensional A C] [IsAbelianGalois A C]
    [FiniteDimensional B D] [IsAbelianGalois B D]
    (x : Bˣ) (n : Aˣ) (hn : LocalFieldTheory.normUnits A B x = n) (z : C) :
    LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom B D x (algebraMap C D z) =
      algebraMap C D (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom A C n z) := by
  let ρ : Gal(D/A) :=
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom B D x).restrictScalars A
  have h := DFunLike.congr_fun
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_norm_restriction A B C D) x
  have hres : ρ.restrictNormal C =
      LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom A C n :=
    h.trans (congrArg (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom A C) hn)
  exact (ρ.restrictNormal_commutes C z).symm.trans
    (congrArg (fun χ : Gal(C/A) => algebraMap C D (χ z)) hres)

variable {k : Type u} {K : Type v} {F : Type w} {L : Type s} {M : Type t}
    [Field k] [Finite k]
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

private def normSquareUpperAction (u : Place k M)
    (x : (u.restrict F).adicCompletionˣ) : u.adicCompletion → u.adicCompletion :=
  let w := u.restrict F
  let _ : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  let _ : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom w.adicCompletion u.adicCompletion x⁻¹

private theorem normSquareUpperAction_apply (u : Place k M)
    (x : (u.restrict F).adicCompletionˣ) (y : M) :
    normSquareUpperAction (F := F) u x (algebraMap M u.adicCompletion y) =
      algebraMap M u.adicCompletion (localArtin (K := F) u x y) :=
  localArtin_completion_apply_universe (K := F) u x y

private def normSquareLowerAction [FiniteDimensional L M] (u : Place k M)
    (n : ((u.restrict L).restrict K).adicCompletionˣ) :
    (u.restrict L).adicCompletion → (u.restrict L).adicCompletion :=
  let z := u.restrict L
  let v := z.restrict K
  let _ : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  let _ : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom v.adicCompletion z.adicCompletion n⁻¹

omit [Algebra K M] [IsScalarTower k K M] [IsScalarTower K L M] [HasPrincipalDivisors k M] in
private theorem normSquareLowerAction_apply [FiniteDimensional L M] (u : Place k M)
    (n : ((u.restrict L).restrict K).adicCompletionˣ) (y : L) :
    normSquareLowerAction (K := K) (L := L) u n (algebraMap L (u.restrict L).adicCompletion y) =
      algebraMap L (u.restrict L).adicCompletion (localArtin (K := K) (u.restrict L) n y) :=
  localArtin_completion_apply_universe (K := K) (u.restrict L) n y

private theorem normSquareCompleted_commutes
    [FiniteDimensional K M] [FiniteDimensional L M] (u : Place k M)
    (x : (u.restrict F).adicCompletionˣ)
    (n : ((u.restrict L).restrict K).adicCompletionˣ)
    (hnValue : n = IdeleGroup.localNormOver ((u.restrict L).restrict K) (u.restrict F)
      ((restrict_restrict (F := K) (E := F) u).trans
        (restrict_restrict (F := K) (E := L) u).symm) x) :
    ∀ y : (u.restrict L).adicCompletion,
      normSquareUpperAction (F := F) u x
        (algebraMap (u.restrict L).adicCompletion u.adicCompletion y) =
        algebraMap (u.restrict L).adicCompletion u.adicCompletion
          (normSquareLowerAction (K := K) (L := L) u n y) := by
  intro y
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
  have hn₀ : LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion x = n :=
    (IdeleGroup.localNormOver_eq_norm v w hw x).symm.trans hnValue.symm
  have hn : LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion x⁻¹ = n⁻¹ :=
    (map_inv (LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion) x).trans
      (congrArg Inv.inv hn₀)
  exact completedNorm_commutes v.adicCompletion w.adicCompletion z.adicCompletion u.adicCompletion
    x⁻¹ n⁻¹ hn y

private theorem localArtin_norm_restrictNormal_core
    [FiniteDimensional K M] [FiniteDimensional L M] (u : Place k M)
    (x : (u.restrict F).adicCompletionˣ)
    (n : ((u.restrict L).restrict K).adicCompletionˣ)
    (hnValue : n = IdeleGroup.localNormOver ((u.restrict L).restrict K) (u.restrict F)
      ((restrict_restrict (F := K) (E := F) u).trans
        (restrict_restrict (F := K) (E := L) u).symm) x) :
    let σ : Gal(M/K) := (localArtin (K := F) u x).restrictScalars K
    let τ : Gal(L/K) := localArtin (K := K) (u.restrict L) n
    AlgEquiv.restrictNormalHom L σ = τ := by
  intro σ τ
  let z : Place k L := u.restrict L
  let iL : L →+* z.adicCompletion := algebraMap L z.adicCompletion
  let iM : M →+* u.adicCompletion := algebraMap M u.adicCompletion
  have hmap (y : L) : algebraMap z.adicCompletion u.adicCompletion (iL y) =
      iM (algebraMap L M y) := IdeleGroup.completionMapOver_algebraMap z u rfl y
  exact restrictNormalHom_eq_of_pointwise_actions (K := K) (L := L) (M := M)
    (E := z.adicCompletion) (T := u.adicCompletion)
    σ τ (normSquareUpperAction (F := F) u x)
    (normSquareLowerAction (K := K) (L := L) u n) iL iM hmap
    (normSquareCompleted_commutes (K := K) (F := F) (L := L) u x n hnValue)
    (fun y => normSquareUpperAction_apply (F := F) u x (algebraMap L M y))
    (normSquareLowerAction_apply (K := K) (L := L) u n)

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
  let n := IdeleGroup.localNormOver ((u.restrict L).restrict K) (u.restrict F)
    ((restrict_restrict (F := K) (E := F) u).trans
      (restrict_restrict (F := K) (E := L) u).symm) x
  exact localArtin_norm_restrictNormal_core u x n rfl

end FunctionField
