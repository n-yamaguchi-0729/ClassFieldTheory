/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Galois restriction under compatible field presentations

Conjugating field automorphisms by compatible algebra isomorphisms commutes
with restriction, including after a degree-one change of the base field.
-/

noncomputable section

namespace ClassFieldTheory

variable {K F L M E U : Type*}
    [Field K] [Field F] [Field L] [Field M] [Field E] [Field U]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K E] [Algebra K U] [Algebra F E] [Algebra F U] [Algebra E U]
    [IsScalarTower K L M] [IsScalarTower K F E] [IsScalarTower K F U]
    [IsScalarTower F E U] [Normal K L] [Normal F E]

/-- Actual restriction commutes with compatible isomorphisms and restriction of scalars. -/
theorem restrictNormal_autCongr_symm_restrictScalars
    (eL : L ≃ₐ[K] E) (eM : M ≃ₐ[K] U)
    (hcomm : ∀ x : L, eM (algebraMap L M x) = algebraMap E U (eL x))
    (σ : Gal(U/F)) :
    AlgEquiv.restrictNormalHom L ((AlgEquiv.autCongr eM).symm (σ.restrictScalars K)) =
      (AlgEquiv.autCongr eL).symm
        ((AlgEquiv.restrictNormalHom E σ).restrictScalars K) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L M).injective
  apply eM.injective
  calc
    eM (algebraMap L M
        ((AlgEquiv.restrictNormalHom L
          ((AlgEquiv.autCongr eM).symm (σ.restrictScalars K))) x)) =
        σ (eM (algebraMap L M x)) := by
      exact (congrArg eM (AlgEquiv.restrictNormal_commutes
        ((AlgEquiv.autCongr eM).symm (σ.restrictScalars K)) L x)).trans
          (eM.apply_symm_apply _)
    _ = σ (algebraMap E U (eL x)) := congrArg σ (hcomm x)
    _ = algebraMap E U ((AlgEquiv.restrictNormalHom E σ) (eL x)) :=
      (AlgEquiv.restrictNormal_commutes σ E (eL x)).symm
    _ = eM (algebraMap L M
        (((AlgEquiv.autCongr eL).symm
          ((AlgEquiv.restrictNormalHom E σ).restrictScalars K)) x)) := by
      rw [hcomm]
      exact congrArg (algebraMap E U) (eL.apply_symm_apply _).symm

/-- The same restriction square commutes on abelianized relative Galois groups. -/
theorem abelianization_restrictNormal_transport
    (hF : Module.finrank K F = 1) (eL : L ≃ₐ[K] E) (eM : M ≃ₐ[K] U)
    (hcomm : ∀ x : L, eM (algebraMap L M x) = algebraMap E U (eL x))
    (z : Abelianization Gal(U/F)) :
    Abelianization.map (AlgEquiv.restrictNormalHom L)
        (((galoisRestrictScalarsEquivOfFinrankOne (E := U) hF).trans
          (AlgEquiv.autCongr eM).symm).abelianizationCongr z) =
      ((galoisRestrictScalarsEquivOfFinrankOne (E := E) hF).trans
        (AlgEquiv.autCongr eL).symm).abelianizationCongr
        (Abelianization.map (AlgEquiv.restrictNormalHom E) z) := by
  refine QuotientGroup.induction_on z ?_
  intro σ
  change Abelianization.of
        (AlgEquiv.restrictNormalHom L
          ((AlgEquiv.autCongr eM).symm (σ.restrictScalars K))) =
      Abelianization.of ((AlgEquiv.autCongr eL).symm
        ((AlgEquiv.restrictNormalHom E σ).restrictScalars K))
  exact congrArg Abelianization.of
      (restrictNormal_autCongr_symm_restrictScalars eL eM hcomm σ)

end ClassFieldTheory
