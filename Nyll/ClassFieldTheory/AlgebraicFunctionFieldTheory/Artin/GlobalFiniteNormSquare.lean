/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalDecomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.UnramifiedFrobeniusRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.OnePlaceDetermination
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteNormProperties
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.OnePlaceNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq

/-!
# Global norm reciprocity in arbitrary finite squares

Outside the two actual conductor supports, arithmetic Frobenius restriction
and the order formula for the actual local norm give reciprocity compatibility.
Weak approximation then determines the continuous class maps everywhere.

-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place IsMulCommutative
open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

namespace FunctionField

private theorem abelianFiniteArtin_placeIdele_eq_frobenius_of_restrict_eq
    {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    (v : Place k K) (z : Place k L) (hz : z.restrict K = v)
    (he : z.ramificationIndex K = 1) (x : v.adicCompletionˣ) :
    abelianFiniteArtin k K L
        (IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
      (unramifiedDecompositionFrobenius (K := K) z he).val ^
        (IdeleGroup.localOrder v x).toAdd := by
  subst v
  exact abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow z he x

private theorem finiteClassNorm_placeIdele
    {k K F : Type} [Field k] [Finite k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K F] [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    (w : Place k F) (x : w.adicCompletionˣ) :
    IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)
      (IdeleClassGroup.mk (k := k) (K := F) (IdeleGroup.placeIdele w x)) =
      IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele (w.restrict K) (IdeleGroup.localNorm (K := K) w x)) := by
  change IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)
      (QuotientGroup.mk (IdeleGroup.placeIdele w x)) =
    QuotientGroup.mk
      (IdeleGroup.placeIdele (w.restrict K) (IdeleGroup.localNorm (K := K) w x))
  exact (IdeleClassGroup.finiteNorm_mk (k := k) (K := K) (L := F)
    (IdeleGroup.placeIdele w x)).trans
      (congrArg (QuotientGroup.mk : IdeleGroup k K → IdeleClassGroup k K)
        (IdeleGroup.norm_placeIdele w x))

variable {k K F L M : Type} [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k F M] [IsScalarTower k L M]
    [IsScalarTower K F M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K F]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- Finite global reciprocity commutes with every actual finite class norm,
including inseparable base extensions, in a compatible finite abelian square. -/
theorem abelianFiniteArtin_finiteNorm_restrictNormal (c : IdeleClassGroup k F) :
    AlgEquiv.restrictNormalHom L ((abelianFiniteArtin k F M c).restrictScalars K) =
      abelianFiniteArtin k K L
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F) c) := by
  classical
  have hKMfinite : FiniteDimensional K M := FiniteDimensional.trans K F M
  have hLMfinite : FiniteDimensional L M := FiniteDimensional.right K L M
  let pL := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := pL.val
  have hkRL : IsScalarTower k (RatFunc k) L := pL.property.1
  have hfunctionL : FunctionField k L := pL.property.2
  let pM := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k F M
  let aRM : Algebra (RatFunc k) M := pM.val
  have hkRM : IsScalarTower k (RatFunc k) M := pM.property.1
  have hfunctionM : FunctionField k M := pM.property.2
  let r : Gal(M/F) →* Gal(L/K) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  let f : IdeleClassGroup k F →ₜ* Gal(L/K) :=
    { toMonoidHom := r.comp (abelianFiniteArtin k F M)
      continuous_toFun := (continuous_of_discreteTopology : Continuous r).comp
        (continuous_abelianFiniteArtin k F M) }
  let g : IdeleClassGroup k F →ₜ* Gal(L/K) :=
    { toMonoidHom := (abelianFiniteArtin k K L).comp
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F))
      continuous_toFun := (continuous_abelianFiniteArtin k K L).comp
        (IdeleClassGroup.continuous_finiteNorm (k := k) (K := K) (L := F)) }
  let mK := RayClass.extensionConductor (k := k) (K := K) (L := L)
  let mF := RayClass.extensionConductor (k := k) (K := F) (L := M)
  let S : Finset (Place k F) :=
    mF.support ∪ mK.support.biUnion (fun v => v.fiberOver F)
  have hfg : f = g := by
    apply IdeleClassGroup.continuousMonoidHom_ext_placeIdele_away f g S
    intro w hw x
    have hwF : w ∉ mF.support := fun hmem => hw (Finset.mem_union_left _ hmem)
    have hwK : w.restrict K ∉ mK.support := by
      intro hmem
      apply hw
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨w.restrict K, hmem, Place.restrict_mem_fiberOver w⟩)
    obtain ⟨u, hu⟩ := Place.exists_restrict_eq (M := M) w
    subst w
    have hrestriction : (u.restrict L).restrict K = (u.restrict F).restrict K :=
      (restrict_restrict (F := K) (E := L) u).trans
        (restrict_restrict (F := K) (E := F) u).symm
    have huUnramified : u.ramificationIndex F = 1 :=
      RayClass.ramificationIndex_eq_one_of_not_mem_support mF le_rfl u hwF
    have hzOutside : (u.restrict L).restrict K ∉ mK.support := by
      rw [hrestriction]
      exact hwK
    have hzUnramified : (u.restrict L).ramificationIndex K = 1 :=
      RayClass.ramificationIndex_eq_one_of_not_mem_support
        mK le_rfl (u.restrict L) hzOutside
    have htop := abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow
      u huUnramified x
    have hbottom := abelianFiniteArtin_placeIdele_eq_frobenius_of_restrict_eq
      ((u.restrict F).restrict K) (u.restrict L) hrestriction hzUnramified
      (IdeleGroup.localNorm (K := K) (u.restrict F) x)
    have hrestrict := unramifiedDecompositionFrobenius_restrictNormal
      (K := K) (F := F) (L := L) u huUnramified hzUnramified
    change r (abelianFiniteArtin k F M
        (IdeleClassGroup.mk (k := k) (K := F)
          (IdeleGroup.placeIdele (u.restrict F) x))) =
      abelianFiniteArtin k K L
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)
          (IdeleClassGroup.mk (k := k) (K := F)
            (IdeleGroup.placeIdele (u.restrict F) x)))
    rw [finiteClassNorm_placeIdele, htop, hbottom, map_zpow]
    change
      (AlgEquiv.restrictNormalHom L
        ((unramifiedDecompositionFrobenius (K := F) u huUnramified).val.restrictScalars K)) ^
          (IdeleGroup.localOrder (u.restrict F) x).toAdd =
        (unramifiedDecompositionFrobenius (K := K) (u.restrict L) hzUnramified).val ^
          (IdeleGroup.localOrder ((u.restrict F).restrict K)
            (IdeleGroup.localNorm (K := K) (u.restrict F) x)).toAdd
    rw [hrestrict, IdeleGroup.localOrder_localNorm_of_finite, ← zpow_natCast, ← zpow_mul]
  exact DFunLike.congr_fun hfg c

end FunctionField
