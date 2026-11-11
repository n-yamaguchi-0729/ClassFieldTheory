/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.PlaceFiberCenterEquivariance
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalInertia
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalCompatibility
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Full local Artin units and the original normalization inertia

The literal integral closure of a place's valuation ring maps to the
valuation ring at an extending place. Its localization at the actual fibre
centre is that valuation ring, and its residue map is surjective. Thus the
original ideal-inertia condition is exactly triviality of the existing
place-decomposition residue action. The local-global Artin comparison then
identifies full local units with this same normalization inertia subgroup.

No residue-action or normalization-inertia comparison is an input. These
statements keep the full local unit group and all wild ramification.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve IsDedekindDomain
open scoped AlgebraicCurve.Place Pointwise

namespace FunctionField

attribute [local instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

private def normalizationToPlaceValuation (w : Place k L) :
    Place.integralClosureAt L (w.restrict K) →+* w.toValuationSubring :=
  (algebraMap (Place.integralClosureAt L (w.restrict K)) L).codRestrict
    w.toValuationSubring.toSubring (Place.forall_mem_of_restrict_eq rfl)

private def normalizationToPlaceResidue (w : Place k L) :
    Place.integralClosureAt L (w.restrict K) →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (normalizationToPlaceValuation (K := K) w)

private theorem normalizationToPlaceResidue_ker (w : Place k L) :
    RingHom.ker (normalizationToPlaceResidue (K := K) w) =
      (Place.fiberCenter L (w.restrict K) (w := w) rfl).asIdeal := by
  ext b
  change IsLocalRing.residue w.toValuationSubring
    (normalizationToPlaceValuation (K := K) w b) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  rfl

private theorem normalizationToPlaceResidue_surjective (w : Place k L) :
    Function.Surjective (normalizationToPlaceResidue (K := K) w) := by
  let B := Place.integralClosureAt L (w.restrict K)
  let q := Place.fiberCenter L (w.restrict K) (w := w) rfl
  let f := normalizationToPlaceValuation (K := K) w
  let : Algebra B w.toValuationSubring := f.toAlgebra
  let e : w.toValuationSubring ≃+* q.valuationSubringAtPrime L :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      (Place.toValuationSubring_eq_of_restrict_eq (w := w) rfl))
  let eB : w.toValuationSubring ≃ₐ[B] q.valuationSubringAtPrime L :=
    { e with commutes' := fun b => Subtype.ext rfl }
  have : IsLocalization.AtPrime w.toValuationSubring q.asIdeal :=
    (IsLocalization.isLocalization_iff_of_algEquiv q.asIdeal.primeCompl eB).mpr
      inferInstance
  have : q.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal q.isPrime q.ne_bot
  let eR := IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal w.toValuationSubring
  intro y
  obtain ⟨b, hb⟩ := eR.surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, hb⟩

private local instance normalizationPlaceAction (w : Place k L) :
    MulSemiringAction Gal(L/K) (Place.integralClosureAt L (w.restrict K)) :=
  IsIntegralClosure.MulSemiringAction (w.restrict K).toValuationSubring K L
    (Place.integralClosureAt L (w.restrict K))

omit [FiniteDimensional K L] in
private theorem normalizationToPlaceResidue_action
    (w : Place k L) (σ : IdeleGroup.decompositionGroup (K := K) w)
    (b : Place.integralClosureAt L (w.restrict K)) :
    IdeleGroup.decompositionResidueAut (K := K) w σ
        (normalizationToPlaceResidue (K := K) w b) =
      normalizationToPlaceResidue (K := K) w (σ.val • b) := by
  change IdeleGroup.decompositionResidueAut (K := K) w σ
      (IsLocalRing.residue w.toValuationSubring (normalizationToPlaceValuation (K := K) w b)) = _
  rw [IdeleGroup.decompositionResidueAut_residue]
  apply congrArg (IsLocalRing.residue w.toValuationSubring)
  apply Subtype.ext
  rw [IdeleGroup.decompositionValuationEquiv_coe]
  exact (algebraMap_galRestrict_apply (w.restrict K).toValuationSubring σ.val b).symm

/-- The full inertia of the original normalization fibre centre is the
included kernel of the actual extending-place residue action. -/
theorem fiberCenter_inertia_eq_residueKernelImage
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : MulSemiringAction Gal(L/K) (Place.integralClosureAt L v) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K L
        (Place.integralClosureAt L v)
    (Place.fiberCenter L v hw).asIdeal.inertia Gal(L/K) =
      (IdeleGroup.decompositionResidueAut (K := K) w).ker.map
        (IdeleGroup.decompositionGroup (K := K) w).subtype := by
  subst v
  intro action
  let q := Place.fiberCenter L (w.restrict K) (w := w) rfl
  let φ := normalizationToPlaceResidue (K := K) w
  have hker : RingHom.ker φ = q.asIdeal := normalizationToPlaceResidue_ker w
  apply Subgroup.ext
  intro σ
  constructor
  · intro hσ
    have hfix : σ ∈ IdeleGroup.decompositionGroup (K := K) w :=
      (Place.fiberCenter_stabilizer_iff (w.restrict K) w rfl σ).mp
        (q.asIdeal.inertia_le_stabilizer hσ)
    let d : IdeleGroup.decompositionGroup (K := K) w := ⟨σ, hfix⟩
    refine ⟨d, ?_, rfl⟩
    change IdeleGroup.decompositionResidueAut (K := K) w d = 1
    apply AlgEquiv.ext
    intro y
    obtain ⟨b, rfl⟩ := normalizationToPlaceResidue_surjective (K := K) w y
    have hb : σ • b - b ∈ RingHom.ker φ := hker.symm ▸ hσ b
    change φ (σ • b - b) = 0 at hb
    rw [map_sub, sub_eq_zero] at hb
    exact (normalizationToPlaceResidue_action w d b).trans hb
  · rintro ⟨d, hd, rfl⟩
    change ∀ b : Place.integralClosureAt L (w.restrict K), d.val • b - b ∈ q.asIdeal
    intro b
    rw [← hker]
    change φ (d.val • b - b) = 0
    rw [map_sub, sub_eq_zero]
    exact (normalizationToPlaceResidue_action w d b).symm.trans
      (DFunLike.congr_fun hd (φ b))

section Reciprocity

variable [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [IsAbelianGalois K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Full local units have image exactly the native ideal inertia at the
same actual place of the finite global extension. -/
theorem localArtin_units_eq_fiberCenter_inertia
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : MulSemiringAction Gal(L/K) (Place.integralClosureAt L v) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K L
        (Place.integralClosureAt L v)
    (RayClass.localHigherUnitGroup (w.restrict K) 0).map
        (localArtin (K := K) w) =
      (Place.fiberCenter L v hw).asIdeal.inertia Gal(L/K) := by
  intro action
  rw [localArtin_units_eq_residue_ker_map,
    fiberCenter_inertia_eq_residueKernelImage v w hw]

/-- The native finite global Artin map carries the original one-place
units onto the same normalization inertia, through its literal idele map. -/
theorem abelianFiniteArtin_placeUnits_eq_fiberCenter_inertia
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : MulSemiringAction Gal(L/K) (Place.integralClosureAt L v) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K L
        (Place.integralClosureAt L v)
    (RayClass.localHigherUnitGroup (w.restrict K) 0).map
        ((abelianFiniteArtin k K L).comp
          (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele (w.restrict K)))) =
      (Place.fiberCenter L v hw).asIdeal.inertia Gal(L/K) := by
  intro action
  have hmap : (abelianFiniteArtin k K L).comp
      (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele (w.restrict K))) =
        localArtin (K := K) w := by
    apply MonoidHom.ext
    intro x
    exact (localArtin_eq_abelianFiniteArtin_placeIdele k K L w x).symm
  rw [hmap]
  exact localArtin_units_eq_fiberCenter_inertia v w hw

end Reciprocity

end FunctionField
