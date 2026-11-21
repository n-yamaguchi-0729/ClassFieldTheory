/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Galois restriction under compatible field presentations

Conjugating field automorphisms by compatible algebra isomorphisms commutes
with restriction, including after a degree-one change of the base field.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe uK uL uM uF uK₀ uL₀ uM₀ uF₀

/-- Conjugation through compatible base and extension ring equivalences
intertwines the actual actions on the extension fields. -/
theorem galEquiv_of_equiv_equiv_apply_equiv
    {K : Type uK} {L : Type uL} {K₀ : Type uK₀} {L₀ : Type uL₀}
    [Field K] [Field L] [Algebra K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (eK : K ≃+* K₀) (eL : L ≃+* L₀)
    (hL : (algebraMap K₀ L₀).comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L))
    (σ : Gal(L₀/K₀)) (x : L) :
    eL (galEquiv_of_equiv_equiv eK eL hL σ x) = σ (eL x) := by
  change eL (eL.symm (σ (eL x))) = σ (eL x)
  exact eL.apply_symm_apply _

/-- Actual normal restriction commutes with conjugation when both the base
field and the extension tower are replaced by compatible ring equivalences.
Each of the six fields may lie in its own universe. -/
theorem restrictNormal_galEquiv_of_equiv_equiv
    {K : Type uK} {L : Type uL} {M : Type uM}
    {K₀ : Type uK₀} {L₀ : Type uL₀} {M₀ : Type uM₀}
    [Field K] [Field L] [Field M] [Field K₀] [Field L₀] [Field M₀]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra K₀ L₀] [Algebra K₀ M₀] [Algebra L₀ M₀] [IsScalarTower K₀ L₀ M₀]
    [Normal K L] [Normal K₀ L₀]
    (eK : K ≃+* K₀) (eL : L ≃+* L₀) (eM : M ≃+* M₀)
    (hL : (algebraMap K₀ L₀).comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L))
    (hM : (algebraMap K₀ M₀).comp eK.toRingHom =
      eM.toRingHom.comp (algebraMap K M))
    (hLM : (algebraMap L₀ M₀).comp eL.toRingHom =
      eM.toRingHom.comp (algebraMap L M))
    (σ : Gal(M₀/K₀)) :
    AlgEquiv.restrictNormalHom L (galEquiv_of_equiv_equiv eK eM hM σ) =
      galEquiv_of_equiv_equiv eK eL hL (AlgEquiv.restrictNormalHom L₀ σ) := by
  have hcomm (x : L) :
      algebraMap L₀ M₀ (eL x) = eM (algebraMap L M x) :=
    DFunLike.congr_fun hLM x
  apply AlgEquiv.ext
  intro x
  apply eL.injective
  apply (algebraMap L₀ M₀).injective
  calc
    algebraMap L₀ M₀ (eL
        (AlgEquiv.restrictNormalHom L (galEquiv_of_equiv_equiv eK eM hM σ) x)) =
        eM (algebraMap L M
          (AlgEquiv.restrictNormalHom L (galEquiv_of_equiv_equiv eK eM hM σ) x)) :=
      hcomm _
    _ = eM (galEquiv_of_equiv_equiv eK eM hM σ (algebraMap L M x)) :=
      congrArg eM (AlgEquiv.restrictNormal_commutes
        (galEquiv_of_equiv_equiv eK eM hM σ) L x)
    _ = σ (eM (algebraMap L M x)) :=
      galEquiv_of_equiv_equiv_apply_equiv eK eM hM σ _
    _ = σ (algebraMap L₀ M₀ (eL x)) := congrArg σ (hcomm x).symm
    _ = algebraMap L₀ M₀ (AlgEquiv.restrictNormalHom L₀ σ (eL x)) :=
      (AlgEquiv.restrictNormal_commutes σ L₀ (eL x)).symm
    _ = algebraMap L₀ M₀ (eL
        (galEquiv_of_equiv_equiv eK eL hL (AlgEquiv.restrictNormalHom L₀ σ) x)) :=
      congrArg (algebraMap L₀ M₀)
        (galEquiv_of_equiv_equiv_apply_equiv eK eL hL
          (AlgEquiv.restrictNormalHom L₀ σ) x).symm

/-- Restricting scalars preserves the same conjugation through compatible
ring equivalences of the two bases and the extension field. -/
theorem restrictScalars_galEquiv_of_equiv_equiv
    {K : Type uK} {F : Type uF} {M : Type uM}
    {K₀ : Type uK₀} {F₀ : Type uF₀} {M₀ : Type uM₀}
    [Field K] [Field F] [Field M] [Field K₀] [Field F₀] [Field M₀]
    [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
    [Algebra K₀ F₀] [Algebra K₀ M₀] [Algebra F₀ M₀] [IsScalarTower K₀ F₀ M₀]
    (eK : K ≃+* K₀) (eF : F ≃+* F₀) (eM : M ≃+* M₀)
    (hK : (algebraMap K₀ M₀).comp eK.toRingHom =
      eM.toRingHom.comp (algebraMap K M))
    (hF : (algebraMap F₀ M₀).comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (σ : Gal(M₀/F₀)) :
    (galEquiv_of_equiv_equiv eF eM hF σ).restrictScalars K =
      galEquiv_of_equiv_equiv eK eM hK (σ.restrictScalars K₀) := by
  apply AlgEquiv.ext
  intro x
  rfl

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
    (z : Group.Abelianization Gal(U/F)) :
    Group.Abelianization.map (AlgEquiv.restrictNormalHom L)
        (((galoisRestrictScalarsEquivOfFinrankOne (E := U) hF).trans
          (AlgEquiv.autCongr eM).symm).abelianizationCongr z) =
      ((galoisRestrictScalarsEquivOfFinrankOne (E := E) hF).trans
        (AlgEquiv.autCongr eL).symm).abelianizationCongr
        (Group.Abelianization.map (AlgEquiv.restrictNormalHom E) z) := by
  refine QuotientGroup.induction_on z ?_
  intro σ
  change Group.Abelianization.of
        (AlgEquiv.restrictNormalHom L
          ((AlgEquiv.autCongr eM).symm (σ.restrictScalars K))) =
      Group.Abelianization.of ((AlgEquiv.autCongr eL).symm
        ((AlgEquiv.restrictNormalHom E σ).restrictScalars K))
  exact congrArg Group.Abelianization.of
      (restrictNormal_autCongr_symm_restrictScalars eL eM hcomm σ)

end ClassFieldTheory
