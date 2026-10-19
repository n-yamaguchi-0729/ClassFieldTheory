/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity

/-!
# Integer valuations and finite unramified Frobenius powers

At an integral valuation value, abstract unramified reciprocity is the
corresponding integer power of arithmetic Frobenius.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)

/-- The finite unramified norm-residue symbol at integer valuation `z` is Frobenius to `z`. -/
theorem normResidueSymbol_unramified_integer
    (H : FiniteAbstractField G) (L : FiniteGaloisSubextension H.field)
    (hu : L.IsUnramified D) (a : ambientFixedAddSubgroup A H.field)
    (z : ℤ) (hz : (v.valuationAt H a : ZHat) = (z : ZHat)) :
    let _ := L.finite
    (D.normResidueSymbol A v hcf H L
      (finiteNormClass A H.field L.field L.below a)).toMul =
      Abelianization.of
        ((L.extensionQuotientMulEquiv.symm
          (D.unramifiedFrobenius (H.toFiniteResidueAbstractField D) L.field L.below)) ^ z) := by
  intro hfinite
  let HR := H.toFiniteResidueAbstractField D
  have hm : (ValuationData.maximalUnramifiedNormResidueSymbol v H a).toMul =
      D.frobenius HR ^ z := by
    apply (D.maximalUnramifiedDegreeEquiv HR).injective
    apply Multiplicative.ext
    rw [map_zpow, D.maximalUnramifiedDegreeEquiv_frobenius]
    change ((D.maximalUnramifiedDegreeEquiv HR
      (ValuationData.maximalUnramifiedNormResidueSymbol v H a).toMul).toAdd : ZHat) =
        z • (1 : ZHat)
    rw [ValuationData.maximalUnramifiedNormResidue_degree, hz, zsmul_eq_mul, mul_one]
  have hs := v.normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction hcf H L hu a
  have hs' := congrArg Additive.toMul hs
  change (D.normResidueSymbol A v hcf H L
      (finiteNormClass A H.field L.field L.below a)).toMul =
    Abelianization.of (D.finiteUnramifiedRestriction HR L hu
      (ValuationData.maximalUnramifiedNormResidueSymbol v H a).toMul) at hs'
  rw [hm, map_zpow, D.finiteUnramifiedRestriction_frobenius] at hs'
  exact hs'

end ClassFormation
