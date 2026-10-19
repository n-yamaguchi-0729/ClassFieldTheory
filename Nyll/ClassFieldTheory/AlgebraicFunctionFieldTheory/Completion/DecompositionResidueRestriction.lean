/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionRestriction

/-!
# Restriction of the actual decomposition action on residue fields

Reduction commutes with restriction along the original valuation rings.
Only the lower extension is assumed Galois; the common upper field may
be an arbitrary finite extension of the base.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional K M]
    [FiniteDimensional L M] [IsGalois K L]

/-- Restriction preserves the stabilizer of the place below. -/
theorem restrictNormal_mem_decompositionGroup (u : Place k M)
    (τ : decompositionGroup (K := K) u) :
    AlgEquiv.restrictNormalHom L τ.val ∈ decompositionGroup (K := K) (u.restrict L) := by
  change SemilinearAut.ofAlgAut
    ((AlgEquiv.restrictNormalHom L τ.val).restrictScalars k) • u.restrict L = u.restrict L
  rw [← restrict_place_algAut_smul (K := K) τ.val u,
    decompositionGroup_smul_eq u τ]

/-- The original residue action commutes with restriction of an actual
upper decomposition automorphism. -/
theorem decompositionResidueAut_restrictNormal (u : Place k M)
    (τ : decompositionGroup (K := K) u)
    (σ : decompositionGroup (K := K) (u.restrict L))
    (hτσ : AlgEquiv.restrictNormalHom L τ.val = σ.val)
    (y : (u.restrict L).ResidueField) :
    u.restrictResidueMap L (decompositionResidueAut (K := K) (u.restrict L) σ y) =
      decompositionResidueAut (K := K) u τ (u.restrictResidueMap L y) := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  rw [decompositionResidueAut_residue, Place.restrictResidueMap_residue,
    Place.restrictResidueMap_residue, decompositionResidueAut_residue]
  congr 1
  apply Subtype.ext
  simp only [Place.coe_restrictInclusion, decompositionValuationEquiv_coe]
  rw [← hτσ]
  exact AlgEquiv.restrictNormal_commutes τ.val L (a : L)

end FunctionField.IdeleGroup
