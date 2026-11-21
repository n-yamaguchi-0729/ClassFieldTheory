/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.FieldEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisDescent
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassH1
public import Nyll.GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport
public import Nyll.GaloisCohomology.Kummer.QuotientTwoCoboundary
public import Nyll.GaloisCohomology.Kummer.QuotientTwoCocycle

/-!
# Inflation and restriction for idèle classes in a finite Galois tower

The standard scalar inclusion identifies lower idèle classes with fixed
upper classes. Its equivariance under field congruence identifies quotient
inflation. Vanishing of subgroup `H¹` then gives middle exactness in degree two.
-/

@[expose] public section

open CategoryTheory ClassFieldTower.Cohomology
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (E : IntermediateField K L) [NumberField E]

local instance standardIdeleClassCommGroup (F : Type) [Field F] [NumberField F] :
    CommGroup (NumberField.IdeleClassGroup (𝓞 F) F) :=
  QuotientGroup.Quotient.commGroup (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)

local notation "StdRep" => standardIdeleClassRep K L
local notation "S" => E.fixingSubgroup
local notation "C_E" => NumberField.IdeleClassGroup (𝓞 E) E
local notation "C_L" => NumberField.IdeleClassGroup (𝓞 L) L
local notation "inc" => NumberField.IdeleClassGroup.fieldInclusion E L

/-- Identifying the fixing subgroup with `Gal(L/E)` preserves the original
idèle class representation on the standard carrier. -/
def standardIdeleClassRelativeCohomologyIso (n : ℕ) :
    groupCohomology (Rep.res (S).subtype StdRep) n ≅
      groupCohomology (standardIdeleClassRep E L) n :=
  groupCohomology.mapIso (A := standardIdeleClassRep E L) (B := Rep.res (S).subtype StdRep)
    E.fixingSubgroupEquiv (LinearEquiv.refl ℤ (Additive C_L)) (fun _ => rfl) n

/-- The original fixing-subgroup restriction on degree-two idèle classes. -/
def standardIdeleClassH2Restrict :
    groupCohomology StdRep 2 ⟶ groupCohomology (standardIdeleClassRep E L) 2 :=
  groupCohomology.map (S).subtype (𝟙 (Rep.res (S).subtype StdRep)) 2 ≫
    (standardIdeleClassRelativeCohomologyIso K L E 2).hom

/-- Scalar inclusion identifies the ordinary lower idèle classes with the fixed upper classes. -/
def standardIdeleClassInvariantsEquiv :
    Additive C_E ≃ₗ[ℤ] (Rep.res (S).subtype StdRep).ρ.invariants := by
  let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  let f := (inc).toAdditive.toIntLinearMap.codRestrict (Rep.res (S).subtype StdRep).ρ.invariants (by
    intro a σ
    have h := (NumberField.IdeleClassGroup.mem_range_fieldInclusion_iff_fixed E L
      (inc a.toMul)).mp ⟨a.toMul, rfl⟩ (E.fixingSubgroupEquiv σ)
    exact congrArg Additive.ofMul h)
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b h
    apply Additive.toMul.injective
    exact NumberField.IdeleClassGroup.fieldInclusion_injective E L
      (congrArg (fun x : (Rep.res (S).subtype StdRep).ρ.invariants => x.val.toMul) h)
  · intro a
    have hf := (NumberField.IdeleClassGroup.mem_range_fieldInclusion_iff_fixed E L a.val.toMul).mpr
      (fun σ => congrArg Additive.toMul (a.property (E.fixingSubgroupEquiv.symm σ)))
    obtain ⟨b, hb⟩ := hf
    exact ⟨Additive.ofMul b, Subtype.ext (congrArg Additive.ofMul hb)⟩

variable [Normal K E]

local notation "ResKer" => MonoidHom.ker (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)

/-- Identify the same fixed classes using the kernel of automorphism restriction. -/
def standardIdeleClassKernelInvariantsEquiv :
    (standardIdeleClassRep K E).V ≃ₗ[ℤ] ((StdRep).quotientToInvariants ResKer).V :=
  (standardIdeleClassInvariantsEquiv K L E).trans
    (LinearEquiv.ofEq _ _ (by rw [E.restrictNormalHom_ker]))

/-- The lower-field cohomology is quotient-group cohomology with fixed
idèle classes, through actual scalar inclusion. -/
def standardIdeleClassQuotientCohomologyIso (n : ℕ) :
    groupCohomology (standardIdeleClassRep K E) n ≅
      groupCohomology ((StdRep).quotientToInvariants ResKer) n := by
  let e := restrictionQuotientEquiv K L E
  let f := standardIdeleClassKernelInvariantsEquiv K L E
  refine groupCohomology.mapIso e.symm f ?_ n
  intro τ
  obtain ⟨q, rfl⟩ := e.surjective τ
  rw [MulEquiv.symm_apply_apply]
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    let a₀ : Additive C_E := a
    change Additive.ofMul (inc (NumberField.IdeleClassGroup.congr
        ((σ.restrictNormal E).restrictScalars ℚ) a₀.toMul)) =
      Additive.ofMul (NumberField.IdeleClassGroup.congr (σ.restrictScalars ℚ) (inc a₀.toMul))
    exact congrArg Additive.ofMul
      (NumberField.IdeleClassGroup.congr_fieldInclusion ((σ.restrictNormal E).restrictScalars ℚ)
        (σ.restrictScalars ℚ) (fun x => (σ.restrictNormal_commutes E x).symm) a₀.toMul).symm

/-- The inflation map with the standard field inclusion on idèle classes. -/
def standardIdeleClassH2Inflate :
    groupCohomology (standardIdeleClassRep K E) 2 ⟶ groupCohomology StdRep 2 :=
  (standardIdeleClassQuotientCohomologyIso K L E 2).hom ≫
    (groupCohomology.infNatTrans ℤ ResKer 2).app StdRep

private theorem standardIdeleClassResKerH1_subsingleton :
    Subsingleton (groupCohomology (Rep.res (ResKer).subtype StdRep) 1) := by
  let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  let : Subsingleton (groupCohomology (standardIdeleClassRep E L) 1) :=
    standardIdeleClassH1_subsingleton E L
  rw [E.restrictNormalHom_ker]
  exact (standardIdeleClassRelativeCohomologyIso K L E 1).toLinearEquiv.injective.subsingleton

/-- The actual inflation map is injective in every finite Galois tower. -/
theorem standardIdeleClassH2Inflate_injective :
    Function.Injective (standardIdeleClassH2Inflate K L E).hom := by
  let : Subsingleton (groupCohomology (Rep.res (ResKer).subtype StdRep) 1) :=
    standardIdeleClassResKerH1_subsingleton K L E
  exact (degreeTwo_inflation_injective StdRep ResKer).comp
    (standardIdeleClassQuotientCohomologyIso K L E 2).toLinearEquiv.injective

/-- An actual degree-two class restricting to zero comes by inflation from
the lower field of the tower. -/
theorem standardIdeleClassH2Restrict_ker_le_inflate_range :
    (standardIdeleClassH2Restrict K L E).hom.ker ≤
      (standardIdeleClassH2Inflate K L E).hom.range := by
  let e := standardIdeleClassRelativeCohomologyIso K L E 2
  let : Subsingleton (groupCohomology (Rep.res (ResKer).subtype StdRep) 1) :=
    standardIdeleClassResKerH1_subsingleton K L E
  intro x hx
  have hxS : (groupCohomology.map (S).subtype (𝟙 (Rep.res (S).subtype StdRep)) 2).hom x = 0 := by
    apply e.toLinearEquiv.injective
    rw [map_zero]
    exact hx
  have hxH :
      (groupCohomology.map (ResKer).subtype (𝟙 (Rep.res (ResKer).subtype StdRep)) 2).hom x = 0 := by
    rw [E.restrictNormalHom_ker]
    exact hxS
  obtain ⟨z, hz⟩ := degreeTwo_restriction_ker_le_inflation_range StdRep ResKer hxH
  let eQ := standardIdeleClassQuotientCohomologyIso K L E 2
  obtain ⟨y, hy⟩ := eQ.toLinearEquiv.surjective z
  refine ⟨y, ?_⟩
  change (groupCohomology.infNatTrans ℤ ResKer 2).app StdRep (eQ.hom y) = x
  rw [← Iso.toLinearEquiv_apply, hy]
  exact hz

/-- Inflation and restriction are exact in the middle on actual degree-two classes. -/
theorem standardIdeleClassH2Restrict_ker_eq_inflate_range :
    (standardIdeleClassH2Restrict K L E).hom.ker =
      (standardIdeleClassH2Inflate K L E).hom.range := by
  apply le_antisymm (standardIdeleClassH2Restrict_ker_le_inflate_range K L E)
  rintro _ ⟨y, rfl⟩
  let e := standardIdeleClassRelativeCohomologyIso K L E 2
  let eQ := standardIdeleClassQuotientCohomologyIso K L E 2
  let z := ((groupCohomology.infNatTrans ℤ ResKer 2).app StdRep).hom (eQ.hom y)
  change e.hom (groupCohomology.map (S).subtype (𝟙 (Rep.res (S).subtype StdRep)) 2 z) = 0
  have h : groupCohomology.map (ResKer).subtype (𝟙 (Rep.res (ResKer).subtype StdRep)) 2 z = 0 :=
    degreeTwo_restrict_inflate_eq_zero StdRep ResKer (eQ.hom y)
  rw [E.restrictNormalHom_ker] at h
  rw [h, map_zero]

end GlobalClassFieldTheory.Cohomology
