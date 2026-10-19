/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements

/-!
# Restriction of norm-residue symbols at a fixed base

The norm-restriction diagram for the identity base extension gives the
restriction formula directly on fixed coefficients. Its right-hand norm
is the identity, so no change of coefficient representative is required.
-/

noncomputable section

namespace ClassFormation

open KummerTheory CyclicCohomology

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Norm-residue symbols commute with restriction to a smaller top field. -/
theorem normResidueSymbol_restriction_finiteNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A) (H : FiniteAbstractField G)
    (L M : FiniteGaloisSubextension H.field)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    let _ := L.finite
    let _ := M.finite
    ∀ a : ambientFixedAddSubgroup A H.field,
      normResidueNaturalityAbelianizedRestriction H.field H.field L.field M.field
          L.below M.below le_rfl hML
          ((D.normResidueSymbol A v hcf H M)
            (finiteNormClass A H.field M.field M.below a)).toMul =
        ((D.normResidueSymbol A v hcf H L)
          (finiteNormClass A H.field L.field L.below a)).toMul := by
  intro hLfinite hMfinite a
  have hself : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field H.field le_rfl) :=
    (FiniteGaloisSubextension.refl H.field).finite
  let T : FiniteAbstractFieldExtension G := ⟨H, H, le_rfl, hself⟩
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_norm_restriction A v hcf T L.field M.field L.below M.below hML)
    (finiteNormClass A H.field M.field M.below a)
  change Additive.ofMul
      (normResidueNaturalityAbelianizedRestriction H.field H.field L.field M.field
        L.below M.below le_rfl hML
        ((D.normResidueSymbol A v hcf H M)
          (finiteNormClass A H.field M.field M.below a)).toMul) =
    (D.normResidueSymbol A v hcf H L)
      (finiteReciprocityNaturalityNormMap A H.field H.field L.field M.field
        L.below M.below le_rfl hML (finiteNormClass A H.field M.field M.below a)) at h
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass, relativeNorm_self] at h
  exact congrArg Additive.toMul h

end ClassFormation
