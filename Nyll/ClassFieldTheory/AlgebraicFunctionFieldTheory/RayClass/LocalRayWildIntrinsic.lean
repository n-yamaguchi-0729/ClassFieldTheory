/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayWildInertia
public import Nyll.EtaleFundamentalGroups.Inertia.ActualWildResidualCore
public import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPowerDetection
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.RingTheory.Ideal.Maximal
public import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Principal-unit Artin images are intrinsic in ordinary-unit images

The original depth-one local Artin image is the existing prime-to-p
residual core of the original ordinary-unit image. The auxiliary absolute
normalization prime is constructed internally and disappears from the
statement. The same characterization survives every continuous image.

Thus the same original continuous absolute-abelian map that preserves
ordinary-unit images also preserves principal-unit images, when the
residue characteristic agrees. No separate wild-preservation condition
is required.
-/

@[expose] public section

noncomputable section

universe u v w u' v'

open AlgebraicCurve LocalClassFieldTheory ProCGroups
open EtaleFundamentalGroups.Inertia

namespace FunctionField.RayClass

attribute [local instance] normalizationCommAlgGaloisAction

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The original principal-unit image is determined by the original
ordinary-unit image and the actual residue characteristic alone. -/
theorem placeArtinUnitImage_one_eq_residualCore (v : Place k K) :
    placeArtinUnitImage v 1 =
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
        (placeArtinUnitImage v 0)).map (placeArtinUnitImage v 0).subtype := by
  let : Algebra v.toValuationSubring (SeparableClosure K) :=
    Algebra.ofSubsemiring v.toValuationSubring
  have : IsScalarTower v.toValuationSubring K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Nontrivial
      (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)) :=
    (inferInstance : Nontrivial (integralClosure v.toValuationSubring (SeparableClosure K)))
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal
    (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)).carrier
  have hQover : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    SchemeTheory.normalizationCommAlgCat_liesOver_maximalIdeal Q
  have : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).IsPrime := hQ.isPrime
  have : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := hQover
  have hp : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have : CharP (IsLocalRing.ResidueField v.toValuationSubring) (ringChar k) :=
    CharP.of_ringHom_of_ne_zero
      ((IsLocalRing.residue v.toValuationSubring).comp (algebraMap k v.toValuationSubring))
      (ringChar k) hp.out.ne_zero
  let f : (actualNormalizationInertiaGroup v.toValuationSubring K
      (SeparableClosure K) Q).carrier →ₜ* localAbsoluteAbelianProfinite K :=
    { toMonoidHom := (localAbsoluteAbelianizationQuotientMap K).comp
        (actualNormalizationInertiaInclusion v.toValuationSubring K
          (SeparableClosure K) Q).hom'
      continuous_toFun := QuotientGroup.continuous_mk.comp continuous_subtype_val }
  have hrange : f.toMonoidHom.range = placeArtinUnitImage v 0 := by
    calc
      f.toMonoidHom.range = placeAbsoluteInertia v Q := by
        change ((localAbsoluteAbelianizationQuotientMap K).comp
          (Q.inertia Gal(SeparableClosure K/K)).subtype).range =
          (Q.inertia Gal(SeparableClosure K/K)).map
            (localAbsoluteAbelianizationQuotientMap K)
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      _ = placeArtinUnitImage v 0 := placeAbsoluteInertia_eq_placeArtinUnitImage v Q
  have hwild : (actualNormalizationWildSubgroup v.toValuationSubring K
      (SeparableClosure K) Q).map f.toMonoidHom = placeArtinUnitImage v 1 := by
    change placeAbsoluteWild v Q = placeArtinUnitImage v 1
    exact placeAbsoluteWild_eq_placeArtinUnitImage v Q
  calc
    placeArtinUnitImage v 1 =
        (actualNormalizationWildSubgroup v.toValuationSubring K
          (SeparableClosure K) Q).map f.toMonoidHom := hwild.symm
    _ = (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
          f.toMonoidHom.range).map f.toMonoidHom.range.subtype :=
      actualNormalizationWildSubgroup_map_eq_rangeResidualCore
        v.toValuationSubring K (SeparableClosure K) Q (ringChar k) f
    _ = (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
          (placeArtinUnitImage v 0)).map (placeArtinUnitImage v 0).subtype :=
      congrArg (fun I : Subgroup (localAbsoluteAbelianProfinite K) =>
        (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ)) I).map
          I.subtype) hrange

variable {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- Passing to any original continuous image preserves the intrinsic
description of the principal-unit image inside its ordinary-unit image. -/
theorem placeArtinUnitImage_one_map_eq_residualCore (v : Place k K)
    (f : localAbsoluteAbelianProfinite K →ₜ* H) :
    (placeArtinUnitImage v 1).map f.toMonoidHom =
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
        ((placeArtinUnitImage v 0).map f.toMonoidHom)).map
          ((placeArtinUnitImage v 0).map f.toMonoidHom).subtype := by
  have : CompactSpace (placeArtinUnitImage v 0) :=
    isCompact_iff_compactSpace.mp (isCompact_placeArtinUnitImage v 0)
  let f' : (placeArtinUnitImage v 0) →ₜ* H :=
    f.comp (ProCGroups.ContinuousMonoidHom.subtype (placeArtinUnitImage v 0))
  have hrange : f'.toMonoidHom.range =
      (placeArtinUnitImage v 0).map f.toMonoidHom := by
    change (f.toMonoidHom.comp (placeArtinUnitImage v 0).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    (placeArtinUnitImage v 1).map f.toMonoidHom =
        (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
          (placeArtinUnitImage v 0)).map f'.toMonoidHom := by
      rw [placeArtinUnitImage_one_eq_residualCore, Subgroup.map_map]
      rfl
    _ = (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
          f'.toMonoidHom.range).map f'.toMonoidHom.range.subtype :=
      ProC.map_sigmaResidualCore_eq_rangeCore ({ringChar k}ᶜ) f'
    _ = (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
          ((placeArtinUnitImage v 0).map f.toMonoidHom)).map
            ((placeArtinUnitImage v 0).map f.toMonoidHom).subtype :=
      congrArg (fun I : Subgroup H =>
        (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ)) I).map
          I.subtype) hrange

variable {k' : Type u'} {K' : Type v'} [Field k'] [Finite k'] [Field K'] [Algebra k' K']
    [Algebra (RatFunc k') K'] [IsScalarTower k' (RatFunc k') K'] [FunctionField k' K']
    [HasPrincipalDivisors k' K']

/-- The same original continuous map that preserves ordinary-unit Artin
images also preserves principal-unit Artin images. -/
theorem placeArtinUnitImage_one_map_eq_of_zero_map_eq
    (v : Place k K) (w : Place k' K')
    (f : localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite K')
    (hchar : ringChar k = ringChar k')
    (hzero : (placeArtinUnitImage v 0).map f.toMonoidHom = placeArtinUnitImage w 0) :
    (placeArtinUnitImage v 1).map f.toMonoidHom = placeArtinUnitImage w 1 := by
  have h := congrArg
    (fun I : Subgroup (localAbsoluteAbelianProfinite K') =>
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ)) I).map I.subtype)
    hzero
  have htarget : (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
      (placeArtinUnitImage w 0)).map (placeArtinUnitImage w 0).subtype =
      placeArtinUnitImage w 1 := by
    rw [hchar]
    exact (placeArtinUnitImage_one_eq_residualCore w).symm
  exact (placeArtinUnitImage_one_map_eq_residualCore v f).trans (h.trans htarget)

end FunctionField.RayClass
