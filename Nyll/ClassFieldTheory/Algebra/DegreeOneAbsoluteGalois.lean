/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotients
public import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

/-!
# Absolute Galois groups under a degree-one field inclusion

The original scalar restriction and the specified separable-closure equivalence give
the same continuous Galois and abelianized maps for independently sized fields.
No function-field reciprocity, chosen replacement field or Artin hypothesis is used.
-/

@[expose] public section

noncomputable section

namespace FunctionField

open LocalClassFieldTheory ProCGroups.Abelian

universe u v

section AbsoluteGroups

variable (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
  [Algebra K (SeparableClosure F)] [IsScalarTower K F (SeparableClosure F)]
  (hKF : Module.finrank K F = 1)
  (eΩ : SeparableClosure F ≃ₐ[K] SeparableClosure K)

/-- Native absolute Galois groups under the actual degree-one scalar map
and the specified comparison of their separable closures. -/
def degreeOneAbsoluteGaloisEquiv :
    Gal(SeparableClosure F/F) ≃ₜ* Gal(SeparableClosure K/K) := by
  have : IsGalois K (SeparableClosure F) := IsGalois.of_algEquiv eΩ.symm
  exact (ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (AlgEquiv.restrictScalarsHom K : Gal(SeparableClosure F/F) →*
      Gal(SeparableClosure F/K))
    (InfiniteGalois.restrictScalarsHom_continuous K F (SeparableClosure F))
    (ClassFieldTheory.galoisRestrictScalars_bijective_of_finrank_one hKF)).trans
    { toMulEquiv := AlgEquiv.autCongr eΩ
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous eΩ
      continuous_invFun :=
        RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_symm_continuous eΩ }

/-- This Galois comparison is literal conjugation on the original closure. -/
theorem degreeOneAbsoluteGaloisEquiv_apply
    (σ : Gal(SeparableClosure F/F)) (x : SeparableClosure K) :
    degreeOneAbsoluteGaloisEquiv K F hKF eΩ σ x = eΩ (σ (eΩ.symm x)) := rfl

/-- The inverse comparison has the inverse literal conjugation formula. -/
theorem degreeOneAbsoluteGaloisEquiv_symm_apply
    (σ : Gal(SeparableClosure K/K)) (x : SeparableClosure F) :
    (degreeOneAbsoluteGaloisEquiv K F hKF eΩ).symm σ x =
      eΩ.symm (σ (eΩ x)) := by
  apply eΩ.injective
  rw [eΩ.apply_symm_apply]
  have h := degreeOneAbsoluteGaloisEquiv_apply K F hKF eΩ
    ((degreeOneAbsoluteGaloisEquiv K F hKF eΩ).symm σ) (eΩ x)
  rw [ContinuousMulEquiv.apply_symm_apply, eΩ.symm_apply_apply] at h
  exact h.symm

/-- The induced comparison of the two original absolute abelian groups. -/
def degreeOneAbsoluteAbelianEquiv :
    localAbsoluteAbelianProfinite F ≃ₜ* localAbsoluteAbelianProfinite K :=
  TopologicalAbelianization.congr (degreeOneAbsoluteGaloisEquiv K F hKF eΩ)

/-- The abelian comparison retains the original Galois representative. -/
theorem degreeOneAbsoluteAbelianEquiv_mk (σ : Gal(SeparableClosure F/F)) :
    degreeOneAbsoluteAbelianEquiv K F hKF eΩ
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite F) =
      QuotientGroup.mk (degreeOneAbsoluteGaloisEquiv K F hKF eΩ σ) := rfl

end AbsoluteGroups

end FunctionField
