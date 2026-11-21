/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClassInflation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClassRestrictionInvariant

/-! # Inflation and restriction of the local fundamental class in finite towers -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology
open ClassFieldTower.Cohomology LocalFieldTheory Module
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

attribute [local instance] stageSeparableClosureAlgebra

variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section SubgroupRestriction

variable (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
  (h : F ≤ E.toIntermediateField) (j : (SeparableClosure K) ≃ₐ[F] SeparableClosure F)

/-- The restriction of the fundamental class has the full order of the
Galois group over the intermediate base. -/
theorem localFundamentalClass_restriction_addOrder :
    let : Algebra F (↥E.toIntermediateField) := nestedStageAlgebra F E h
    let : IsScalarTower K F (↥E.toIntermediateField) := nestedStageTower F E h
    let : FiniteDimensional F (↥E.toIntermediateField) := nestedStageFinite F E h
    addOrderOf (relativeBaseRestriction K F E (localFundamentalClass K E)) = finrank F E := by
  intro algebraOwner towerOwner finiteOwner
  let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let j₀ := IsSepClosure.equiv F (SeparableClosure K) (SeparableClosure F)
  let f := relativeStageAbsoluteInflation F E h j₀
  let c := relativeBaseRestriction K F E (localFundamentalClass K E)
  let e := localBrauerInvariantEquiv F
  let q : AddCircle (1 : ℚ) := (((1 : ℚ) / (finrank F E : ℕ) : ℚ) : AddCircle (1 : ℚ))
  have hf : Function.Injective f := relativeStageAbsoluteInflation_injective F E h j₀
  have hInvariant : e (f c) = q := localFundamentalClass_restriction_invariant K E F h j₀
  let : Module.Free F (↥E.toIntermediateField) :=
    Module.Free.of_divisionRing (K := F) (V := ↥E.toIntermediateField)
  have hDegree : 0 < finrank F E :=
    (Module.finrank_pos_iff_of_free F (↥E.toIntermediateField)).mpr inferInstance
  have hPeriod : addOrderOf q = finrank F E :=
    AddCircle.addOrderOf_period_div (p := (1 : ℚ)) hDegree
  exact (addOrderOf_injective f hf c).symm.trans
    ((addOrderOf_injective e.toAddMonoidHom e.injective (f c)).symm.trans
      ((congrArg addOrderOf hInvariant).trans hPeriod))

/-- Every original relative class over the intermediate base is an
integer multiple of the restricted fundamental class. -/
theorem localFundamentalClass_restriction_generates :
    let : Algebra F (↥E.toIntermediateField) := nestedStageAlgebra F E h
    let : IsScalarTower K F (↥E.toIntermediateField) := nestedStageTower F E h
    let : FiniteDimensional F (↥E.toIntermediateField) := nestedStageFinite F E h
    ∀ c : continuousCohomology 2 (galoisUnitsRep F E),
      ∃ m : ℤ, m • relativeBaseRestriction K F E (localFundamentalClass K E) = c := by
  intro algebraOwner towerOwner finiteOwner
  let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
  let e := continuousRelativeUnitsH2Equiv F E
  let z := relativeBaseRestriction K F E (localFundamentalClass K E)
  let S := AddSubgroup.zmultiples z
  obtain ⟨hfinite, hbound⟩ := finiteLocalUnitsH2_finite_card_le F E
  let : Finite (groupCohomology (liftedGaloisUnitsRep F E) 2) := hfinite
  let : Finite (continuousCohomology 2 (galoisUnitsRep F E)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card (continuousCohomology 2 (galoisUnitsRep F E)) ≤ Nat.card S := by
    have ht : Nat.card S = finrank F E :=
      (Nat.card_zmultiples z).trans (localFundamentalClass_restriction_addOrder K E F h)
    exact (Nat.card_congr e.toEquiv).le.trans (hbound.trans ht.symm.le)
  have hsurj : Function.Surjective S.subtype :=
    (S.subtype_injective.bijective_of_nat_card_le hcard).2
  change ∀ c : continuousCohomology 2 (galoisUnitsRep F E), ∃ m : ℤ, m • z = c
  intro c
  obtain ⟨a, ha⟩ := hsurj c
  obtain ⟨m, hm⟩ := a.property
  exact ⟨m, hm.trans ha⟩

end SubgroupRestriction

end ClassFieldTheory.Brauer
