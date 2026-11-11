/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayWildIntrinsic
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore

/-!
# Comparing original principal-unit images in a common quotient

Two original absolute-abelian groups need not be related by a map. Their
maps into the same Hausdorff topological group suffice: equal ordinary-unit
images determine equal principal-unit images in the same characteristic.
This applies directly to the original fundamental-group abelianization.
-/

@[expose] public section

noncomputable section

universe u v u' v' w

open AlgebraicCurve LocalClassFieldTheory ProCGroups

namespace FunctionField.RayClass

variable {k : Type u} {K : Type v} {k' : Type u'} {K' : Type v'}
    [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]
    [Field k'] [Finite k'] [Field K'] [Algebra k' K']
    [Algebra (RatFunc k') K'] [IsScalarTower k' (RatFunc k') K'] [FunctionField k' K']
    [HasPrincipalDivisors k' K']
    {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- Equality of the original ordinary-unit images through two actual
continuous quotient maps forces equality of their principal-unit images. -/
theorem placeArtinUnitImage_one_map_eq_of_zero_images_eq
    (v : Place k K) (w : Place k' K')
    (f : localAbsoluteAbelianProfinite K →ₜ* H)
    (g : localAbsoluteAbelianProfinite K' →ₜ* H)
    (hchar : ringChar k = ringChar k')
    (hzero : (placeArtinUnitImage v 0).map f.toMonoidHom =
      (placeArtinUnitImage w 0).map g.toMonoidHom) :
    (placeArtinUnitImage v 1).map f.toMonoidHom =
      (placeArtinUnitImage w 1).map g.toMonoidHom := by
  have h := congrArg
    (fun I : Subgroup H =>
      (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ)) I).map I.subtype)
    hzero
  have htarget : (ProC.proCResidualCore (FiniteGroupClass.sigmaGroup ({ringChar k}ᶜ))
      ((placeArtinUnitImage w 0).map g.toMonoidHom)).map
        ((placeArtinUnitImage w 0).map g.toMonoidHom).subtype =
      (placeArtinUnitImage w 1).map g.toMonoidHom := by
    rw [hchar]
    exact (placeArtinUnitImage_one_map_eq_residualCore w g).symm
  exact (placeArtinUnitImage_one_map_eq_residualCore v f).trans (h.trans htarget)

end FunctionField.RayClass
