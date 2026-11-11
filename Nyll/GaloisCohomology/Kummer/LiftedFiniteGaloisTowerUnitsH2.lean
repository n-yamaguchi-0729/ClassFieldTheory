/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedUnitsH2Inflation
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomologyTransport
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Actual unit H² maps in arbitrary field towers

Lifted integer coefficients permit the original upper fields in a common arbitrary
universe, independently of the base fields. Field range descent uses the same
inclusion, its actual range, and its specified equivalence. Relative restriction
keeps the upper-field units unchanged. The final field in the naturality squares
may be a completion.
-/

@[expose] public section

universe u v w
open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K : Type v) (F N : Type u) [Field K] [Field F] [Field N]
  [Algebra K F] [Algebra F N] [Algebra K N] [IsScalarTower K F N]

/-- Inclusion of units in a normal field tower, equivariant for restriction. -/
def liftedFiniteGaloisTowerUnitsInflationRepHom [Normal K F] :
    Rep.res (AlgEquiv.restrictNormalHom F) (liftedGaloisUnitsRep K F) ⟶
      liftedGaloisUnitsRep K N := by
  apply Rep.ofHom
  refine ⟨(ModuleCat.coefficientRingAddHom
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    (M := ModuleCat.of ℤ (Additive Fˣ)) (N := ModuleCat.of ℤ (Additive Nˣ))
    (Units.map (algebraMap F N).toMonoidHom).toAdditive).hom, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply Units.ext
  exact σ.restrictNormal_commutes F ((show Additive Fˣ from a).toMul : F)

/-- Inflation induced by restricting automorphisms and including field units. -/
def liftedFiniteGaloisTowerUnitsH2Inflation [Normal K F] :
    groupCohomology (liftedGaloisUnitsRep K F) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep K N) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom F)
    (liftedFiniteGaloisTowerUnitsInflationRepHom K F N) 2

/-- Relative restriction leaves upper-field units unchanged. -/
def liftedFiniteGaloisTowerUnitsRestrictionRepHom
    (K : Type v) (F : Type w) (N : Type u) [Field K] [Field F] [Field N]
    [Algebra K F] [Algebra F N] [Algebra K N] [IsScalarTower K F N] :
    Rep.res (AlgEquiv.restrictScalarsHom K) (liftedGaloisUnitsRep K N) ⟶
      liftedGaloisUnitsRep F N :=
  Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩

/-- Restriction to the relative Galois group, with identical unit coefficients. -/
def liftedFiniteGaloisTowerUnitsH2Restriction
    (K : Type v) (F : Type w) (N : Type u) [Field K] [Field F] [Field N]
    [Algebra K F] [Algebra F N] [Algebra K N] [IsScalarTower K F N] :
    groupCohomology (liftedGaloisUnitsRep K N) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep F N) 2 :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (liftedFiniteGaloisTowerUnitsRestrictionRepHom K F N) 2

private theorem lifted_restriction_intermediateField (E : IntermediateField K N) :
    liftedFiniteGaloisUnitsH2Restriction K N E =
      liftedFiniteGaloisTowerUnitsH2Restriction K E N := by
  let ψ : Rep.res E.fixingSubgroupEquiv.symm.toMonoidHom
      (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K N)) ⟶
      liftedGaloisUnitsRep E N := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  change groupCohomology.map E.fixingSubgroup.subtype
      (𝟙 (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K N))) 2 ≫
    groupCohomology.map E.fixingSubgroupEquiv.symm.toMonoidHom ψ 2 =
      liftedFiniteGaloisTowerUnitsH2Restriction K E N
  refine (groupCohomology.map_comp
    (A := liftedGaloisUnitsRep K N)
    (B := Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K N))
    (C := liftedGaloisUnitsRep E N) E.fixingSubgroup.subtype
    E.fixingSubgroupEquiv.symm.toMonoidHom
    (𝟙 (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K N))) ψ 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro a
    rfl

private theorem lifted_fieldRange_inflation [Normal K F]
    [Normal K (IsScalarTower.toAlgHom K F N).fieldRange] :
    (liftedUnitsCohomologyCongrTop K F (IsScalarTower.toAlgHom K F N).fieldRange
      (IsScalarTower.toAlgHom K F N).equivFieldRange 2).hom ≫
        liftedFiniteGaloisUnitsH2Inflation K N (IsScalarTower.toAlgHom K F N).fieldRange =
      liftedFiniteGaloisTowerUnitsH2Inflation K F N := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  let E : IntermediateField K N := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  let φ : Rep.res (AlgEquiv.autCongr e).symm.toMonoidHom
      (liftedGaloisUnitsRep K F) ⟶ liftedGaloisUnitsRep K E := by
    apply Rep.ofHom
    refine ⟨(liftedUnitsMapEquivLinear K F E e).toLinearMap, ?_⟩
    intro σ
    apply LinearMap.ext
    intro a
    apply Units.ext
    change e (e.symm (σ (e ((show Additive Fˣ from a).toMul : F)))) =
      σ (e ((show Additive Fˣ from a).toMul : F))
    exact e.apply_symm_apply _
  change groupCohomology.map (AlgEquiv.autCongr e).symm.toMonoidHom φ 2 ≫
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (liftedFiniteGaloisUnitsInflationRepHom K N E) 2 =
    liftedFiniteGaloisTowerUnitsH2Inflation K F N
  refine (groupCohomology.map_comp
    (A := liftedGaloisUnitsRep K F) (B := liftedGaloisUnitsRep K E)
    (C := liftedGaloisUnitsRep K N) (AlgEquiv.autCongr e).symm.toMonoidHom
    (AlgEquiv.restrictNormalHom E) φ (liftedFiniteGaloisUnitsInflationRepHom K N E) 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    change algebraMap F N (e.symm (σ.restrictNormal E (e x))) =
      algebraMap F N (σ.restrictNormal F x)
    have heval (y : E) : algebraMap F N (e.symm y) = (y : N) :=
      congrArg (fun z : E ↦ (z : N)) (e.apply_symm_apply y)
    rw [heval]
    exact (σ.restrictNormal_commutes E (e x)).trans
      (σ.restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    rfl

/-- Field-unit inflation is injective for an arbitrary finite Galois tower. -/
theorem liftedFiniteGaloisTowerUnitsH2Inflation_injective
    [Normal K F] [FiniteDimensional K N] [IsGalois K N] :
    Function.Injective (liftedFiniteGaloisTowerUnitsH2Inflation K F N).hom := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  have : Normal K i.fieldRange := Normal.of_algEquiv i.equivFieldRange
  let c := liftedUnitsCohomologyCongrTop K F i.fieldRange i.equivFieldRange 2
  intro x y hxy
  apply c.toLinearEquiv.injective
  apply liftedFiniteGaloisUnitsH2Inflation_injective K N i.fieldRange
  have hx := congrArg (fun f ↦ f.hom x) (lifted_fieldRange_inflation K F N)
  have hy := congrArg (fun f ↦ f.hom y) (lifted_fieldRange_inflation K F N)
  exact hx.trans (hxy.trans hy.symm)

private theorem lifted_restriction_surjectiveScalars
    (E : Type w) [Field E] [Algebra K E] [Algebra E N] [IsScalarTower K E N]
    [Algebra F E] [IsScalarTower F E N]
    (h : Function.Surjective (algebraMap F E)) :
    liftedFiniteGaloisTowerUnitsH2Restriction K E N ≫
      (liftedUnitsCohomologyRestrictScalarsIso F E N h 2).hom =
        liftedFiniteGaloisTowerUnitsH2Restriction K F N := by
  let t : Gal(N/F) ≃* Gal(N/E) := AlgEquiv.extendScalarsHomOfSurjective h
  let ψ : Rep.res t.toMonoidHom (liftedGaloisUnitsRep E N) ⟶
      liftedGaloisUnitsRep F N := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  change groupCohomology.map (AlgEquiv.restrictScalarsHom K)
      (liftedFiniteGaloisTowerUnitsRestrictionRepHom K E N) 2 ≫
    groupCohomology.map t.toMonoidHom ψ 2 =
      liftedFiniteGaloisTowerUnitsH2Restriction K F N
  refine (groupCohomology.map_comp
    (A := liftedGaloisUnitsRep K N) (B := liftedGaloisUnitsRep E N)
    (C := liftedGaloisUnitsRep F N) (AlgEquiv.restrictScalarsHom K)
    t.toMonoidHom (liftedFiniteGaloisTowerUnitsRestrictionRepHom K E N) ψ 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro a
    rfl

/-- Middle exactness for unit H² in an arbitrary finite Galois tower. -/
theorem liftedFiniteGaloisTowerUnitsH2Restriction_ker_le_inflation_range
    [Normal K F] [FiniteDimensional K N] [IsGalois K N] :
    (liftedFiniteGaloisTowerUnitsH2Restriction K F N).hom.ker ≤
      (liftedFiniteGaloisTowerUnitsH2Inflation K F N).hom.range := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  let E : IntermediateField K N := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  have : Normal K E := Normal.of_algEquiv e
  let : Algebra F E := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hsur : Function.Surjective (algebraMap F E) := e.surjective
  let c := liftedUnitsCohomologyRestrictScalarsIso F E N hsur 2
  intro x hx
  have hxE : (liftedFiniteGaloisUnitsH2Restriction K N E).hom x = 0 := by
    rw [lifted_restriction_intermediateField K N E]
    apply c.toLinearEquiv.injective
    rw [map_zero]
    exact (congrArg (fun f : groupCohomology (liftedGaloisUnitsRep K N) 2 ⟶
        groupCohomology (liftedGaloisUnitsRep F N) 2 ↦ f.hom x)
      (lifted_restriction_surjectiveScalars K F N E hsur)).trans hx
  obtain ⟨y, hy⟩ := liftedFiniteGaloisUnitsH2Restriction_ker_le_inflation_range K N E hxE
  let d := liftedUnitsCohomologyCongrTop K F E e 2
  refine ⟨d.inv y, ?_⟩
  have hinf := congrArg (fun f ↦ f.hom (d.inv y)) (lifted_fieldRange_inflation K F N)
  have hcancel : d.hom (d.inv y) = y := d.toLinearEquiv.apply_symm_apply y
  exact hinf.symm.trans
    ((congrArg (fun z ↦ (liftedFiniteGaloisUnitsH2Inflation K N E).hom z) hcancel).trans hy)

/-- Successive actual unit inflations equal direct inflation along the field tower. -/
theorem liftedFiniteGaloisTowerUnitsH2Inflation_trans
    (K : Type v) (F M N : Type u) [Field K] [Field F] [Field M] [Field N]
    [Algebra K F] [Algebra K M] [Algebra K N]
    [Algebra F M] [Algebra F N] [Algebra M N]
    [IsScalarTower K F M] [IsScalarTower K F N] [IsScalarTower K M N]
    [IsScalarTower F M N] [Normal K F] [Normal K M] :
    liftedFiniteGaloisTowerUnitsH2Inflation K F M ≫ liftedFiniteGaloisTowerUnitsH2Inflation K M N =
      liftedFiniteGaloisTowerUnitsH2Inflation K F N := by
  rw [liftedFiniteGaloisTowerUnitsH2Inflation, liftedFiniteGaloisTowerUnitsH2Inflation,
    liftedFiniteGaloisTowerUnitsH2Inflation, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    calc
      algebraMap F N ((σ.restrictNormal M).restrictNormal F x) =
          algebraMap M N (algebraMap F M ((σ.restrictNormal M).restrictNormal F x)) :=
        IsScalarTower.algebraMap_apply F M N _
      _ = algebraMap M N ((σ.restrictNormal M) (algebraMap F M x)) :=
        congrArg (algebraMap M N) ((σ.restrictNormal M).restrictNormal_commutes F x)
      _ = σ (algebraMap M N (algebraMap F M x)) :=
        σ.restrictNormal_commutes M (algebraMap F M x)
      _ = σ (algebraMap F N x) :=
        congrArg σ (IsScalarTower.algebraMap_apply F M N x).symm
      _ = algebraMap F N (σ.restrictNormal F x) := (σ.restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F M N ((show Additive Fˣ from a).toMul : F)).symm

/-- Localization through an intermediate normal upper field agrees with direct
localization. The intermediate upper field need not be normal over the original base. -/
theorem liftedFiniteGaloisTowerUnitsH2BaseChange_trans
    (K : Type v) (F : Type u) (E : Type w) (M N : Type u)
    [Field K] [Field F] [Field E] [Field M] [Field N]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra K N]
    [Algebra F M] [Algebra F N] [Algebra E M] [Algebra E N] [Algebra M N]
    [IsScalarTower K F M] [IsScalarTower K F N] [IsScalarTower K M N]
    [IsScalarTower K E M] [IsScalarTower K E N]
    [IsScalarTower F M N] [IsScalarTower E M N] [Normal K F] [Normal E M] :
    (liftedFiniteGaloisTowerUnitsH2Inflation K F M ≫
      liftedFiniteGaloisTowerUnitsH2Restriction K E M) ≫
        liftedFiniteGaloisTowerUnitsH2Inflation E M N =
      liftedFiniteGaloisTowerUnitsH2Inflation K F N ≫
      liftedFiniteGaloisTowerUnitsH2Restriction K E N := by
  simp only [liftedFiniteGaloisTowerUnitsH2Inflation, liftedFiniteGaloisTowerUnitsH2Restriction]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    calc
      algebraMap F N (((σ.restrictNormal M).restrictScalars K).restrictNormal F x) =
          algebraMap M N (algebraMap F M
            (((σ.restrictNormal M).restrictScalars K).restrictNormal F x)) :=
        IsScalarTower.algebraMap_apply F M N _
      _ = algebraMap M N ((σ.restrictNormal M) (algebraMap F M x)) :=
        congrArg (algebraMap M N)
          (((σ.restrictNormal M).restrictScalars K).restrictNormal_commutes F x)
      _ = σ (algebraMap M N (algebraMap F M x)) :=
        σ.restrictNormal_commutes M (algebraMap F M x)
      _ = σ (algebraMap F N x) :=
        congrArg σ (IsScalarTower.algebraMap_apply F M N x).symm
      _ = algebraMap F N ((σ.restrictScalars K).restrictNormal F x) :=
        ((σ.restrictScalars K).restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply F M N ((show Additive Fˣ from a).toMul : F)).symm

end
end ClassFieldTower.Cohomology
