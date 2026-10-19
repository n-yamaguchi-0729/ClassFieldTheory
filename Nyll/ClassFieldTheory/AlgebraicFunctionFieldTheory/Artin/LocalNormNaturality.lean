/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Separable
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2Over
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Local Artin symbols and norms in actual function-field towers

The norm--restriction law for local reciprocity is applied to the actual
completed field tower. Evaluation on the dense original field identifies
the resulting completed automorphisms with the original decomposition
automorphisms. The arithmetic convention inverts both local inputs, and
the genuine field norm respects this inversion.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

private theorem localArtinMonoidHom_norm_tower
    (F E T : Type) [Field F] [Field E] [Field T]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [Algebra F T] [Algebra E T] [IsScalarTower F E T]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [(ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation E)]
    [FiniteDimensional F T] [IsAbelianGalois F T]
    [FiniteDimensional E T] [IsAbelianGalois E T] (x : Eˣ) :
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom E T x).restrictScalars F =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom F T
        (LocalFieldTheory.normUnits F E x) := by
  have h := DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction F E T T) x
  apply AlgEquiv.ext
  intro y
  have heval := congrArg (fun σ : Gal(T/F) => σ y) h
  have hself := AlgEquiv.restrictNormal_commutes
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom E T x |>.restrictScalars F) T y
  exact hself.symm.trans heval

section CompletionEvaluation

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual local Artin automorphism acts on the embedded original field
by the existing local reciprocity map with the arithmetic input convention. -/
theorem localArtin_completion_apply (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) (y : L) :
    let _ : ValuativeRel (w.restrict K).adicCompletion :=
      placeCompletionValuativeRel (w.restrict K)
    let _ : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField (w.restrict K)
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (w.restrict K).adicCompletion w.adicCompletion x⁻¹
        (algebraMap L w.adicCompletion y) =
      algebraMap L w.adicCompletion (localArtin (K := K) w x y) := by
  intro hrelation hlocal
  have h := localDecompositionArtin_completion (K := K) w x
  exact (congrArg (fun σ : Gal(w.adicCompletion/(w.restrict K).adicCompletion) =>
    σ (algebraMap L w.adicCompletion y)) h).symm.trans
      (IdeleGroup.decompositionCompletionEquiv_algebraMap w
        (localDecompositionArtin (K := K) w x) y)

end CompletionEvaluation

section Tower

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k K L M : Type} [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) L]
    [IsScalarTower (RatFunc k) K L] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- In a finite abelian tower, applying the lower local Artin symbol to
the actual local norm gives the upper local symbol with scalars restricted.
The place equality is supplied by restriction transitivity. -/
theorem localArtin_norm_restrictScalars (u : Place k M) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    let _ : IsAbelianGalois L M := IsAbelianGalois.tower_top K L M
    let _ : FunctionField k L := FiniteDimensional.trans (RatFunc k) K L
    ∀ x : (u.restrict L).adicCompletionˣ,
      (localArtin (K := L) u x).restrictScalars K =
        localArtin (K := K) u
          (IdeleGroup.localNormOver (u.restrict K) (u.restrict L)
            (restrict_restrict (F := K) (E := L) u) x) := by
  intro hLMfinite hLMabelian hLfunction x
  have hKLabelian : IsAbelianGalois K L := IsAbelianGalois.tower_bot K L M
  let v : Place k K := u.restrict K
  let w : Place k L := u.restrict L
  have hw : w.restrict K = v := restrict_restrict (F := K) (E := L) u
  let avw : Algebra v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionMapOver v w hw).toAlgebra
  let rv : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  let rw' : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have hvlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hwlocal : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  have hvwfinite : FiniteDimensional v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteGaloisOver v w hw).1
  have hvwgalois : IsGalois v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteGaloisOver v w hw).2
  have hvwextension : (ValuativeRel.valuation v.adicCompletion).HasExtension
      (ValuativeRel.valuation w.adicCompletion) :=
    IdeleGroup.completionCanonical_hasExtension_over v w hw
  have hvwu : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (IdeleGroup.completionMapOver_trans v w u hw rfl rfl)).symm)
  let n : v.adicCompletionˣ := IdeleGroup.localNormOver v w hw x
  have hn : LocalFieldTheory.normUnits v.adicCompletion w.adicCompletion x⁻¹ =
      n⁻¹ := by
    rw [map_inv]
    exact congrArg Inv.inv (IdeleGroup.localNormOver_eq_norm v w hw x).symm
  have hlocal := localArtinMonoidHom_norm_tower
    v.adicCompletion w.adicCompletion u.adicCompletion x⁻¹
  rw [hn] at hlocal
  apply AlgEquiv.ext
  intro y
  apply (algebraMap M u.adicCompletion).injective
  have heval := congrArg
    (fun σ : Gal(u.adicCompletion/v.adicCompletion) =>
      σ (algebraMap M u.adicCompletion y)) hlocal
  exact (localArtin_completion_apply (K := L) u x y).symm.trans
    (heval.trans (localArtin_completion_apply (K := K) u n y))

end Tower

end FunctionField
