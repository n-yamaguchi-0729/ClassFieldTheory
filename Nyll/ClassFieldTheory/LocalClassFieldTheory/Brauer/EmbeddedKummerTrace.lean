/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerTrace
public import Nyll.GaloisCohomology.Topology.ContinuousCupCorestriction

/-! # Kummer trace across an embedded finite local extension -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

attribute [local instance] stageSeparableClosureAlgebra

variable (K : Type u) [Field K]
variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
variable (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

local notation "G" => Gal(SeparableClosure K/K)
local notation "G'" => Gal(SeparableClosure E/E)
local notation "H" => stageOpenFixingSubgroup K E
local notation "I" => OpenSubgroup.toSubgroup (stageOpenFixingSubgroup K E)
local notation "R" X => TopRep.res (Subgroup.subtype (OpenSubgroup.toSubgroup
  (stageOpenFixingSubgroup K E))) X

private theorem nsmul_hom_eq_zero_of_nsmul_eq_zero
    {A B : Type*} [AddMonoid A] [AddMonoid B] (f : A →+ B)
    (n : ℕ) (x : A) (hx : n • x = 0) : n • f x = 0 :=
  (map_nsmul f n x).symm.trans ((congrArg f hx).trans (map_zero f))

/-- The actual closure comparison transports roots of unity by restriction
of the same map used on unit coefficients. -/
def embeddedMuTransport (n : ℕ) :
    TopRep.res (embeddedAbsoluteRestrictionEquiv K E j).symm.toMonoidHom (separableMuTopRep E n) ⟶
      R (separableMuTopRep K n) := by
  let e := embeddedAbsoluteRestrictionEquiv K E j
  let f := embeddedUnitsTransport K E j
  let M := TopRep.res e.symm.toMonoidHom (separableMuTopRep E n)
  let N := R (separableMuTopRep K n)
  let φ : M →ₗ[ℤ] N :=
    { toFun := fun a => ⟨f.hom a.val, by
        let b : unitsRep E := a.val
        have hb : n • b = 0 := a.property
        exact nsmul_hom_eq_zero_of_nsmul_eq_zero f.hom.toAddMonoidHom n b hb⟩
      map_add' := fun a b => Subtype.ext (map_add f.hom a.val b.val)
      map_smul' := fun m a => Subtype.ext (map_smul f.hom m a.val) }
  exact TopRep.ofHom {
    toLinearMap := φ
    cont := continuous_of_discreteTopology
    isIntertwining' := fun σ => by
      apply ContinuousLinearMap.ext
      intro a
      exact Subtype.ext (TopRep.hom_comm_apply f σ a.val) }

theorem embeddedMuTransport_val (n : ℕ) (a : separableMuTopRep E n) :
    (embeddedMuTransport K E j n a).val = embeddedUnitsTransport K E j a.val := rfl

private theorem addMonoidHom_bijective_nsmul_torsion
    {A B : Type*} [AddMonoid A] [AddMonoid B] (f : A →+ B)
    (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (fun a : {a : A // n • a = 0} =>
      (⟨f a.val, nsmul_hom_eq_zero_of_nsmul_eq_zero f n a.val a.property⟩ :
        {b : B // n • b = 0})) := by
  constructor
  · intro a b hab
    exact Subtype.ext (hf.injective (congrArg Subtype.val hab))
  · intro b
    obtain ⟨a, ha⟩ := hf.surjective b.val
    have hz : n • a = 0 := hf.injective (by rw [map_nsmul, ha, b.property, map_zero])
    exact ⟨⟨a, hz⟩, Subtype.ext ha⟩

/-- Every root of unity transports bijectively, of the same order. -/
theorem embeddedMuTransport_bijective (n : ℕ) :
    Function.Bijective (embeddedMuTransport K E j n) := by
  let f := embeddedUnitsTransport K E j
  let jInv : SeparableClosure E ≃ₐ[E] SeparableClosure K := j.symm
  let u : (SeparableClosure E)ˣ ≃* (SeparableClosure K)ˣ :=
    Units.mapEquiv jInv.toRingEquiv.toMulEquiv
  have hbij : Function.Bijective f.hom.toAddMonoidHom := u.toAdditive.bijective
  exact addMonoidHom_bijective_nsmul_torsion f.hom.toAddMonoidHom hbij n

/-- Transport degree-two root-of-unity classes along the actual closure identification. -/
def embeddedMuCohomologyTransport (n : ℕ) :
    continuousCohomology 2 (separableMuTopRep E n) →+
      continuousCohomology 2 (R (separableMuTopRep K n)) := by
  let f := map (X := separableMuTopRep E n) (Y := R (separableMuTopRep K n))
    (embeddedAbsoluteRestrictionInverseHom K E j) (embeddedMuTransport K E j n) 2
  exact f.hom.toLinearMap.toAddMonoidHom

private def embeddedMuInclusionH2 (n : ℕ) :
    continuousCohomology 2 (R (separableMuTopRep K n)) →+
      continuousCohomology 2 (R (unitsRep K)) := by
  let f := map (X := R (separableMuTopRep K n)) (Y := R (unitsRep K))
    (ContinuousMonoidHom.id I)
    ((TopRep.resFunctor (I).subtype).map (separableMuInclusion K n)) 2
  exact f.hom.toLinearMap.toAddMonoidHom

private theorem cohomology_addHom_comp_apply
    {G₀ G₁ G₂ : Type u} [Group G₀] [Group G₁] [Group G₂]
    [TopologicalSpace G₀] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₀] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    {A : TopRep.{u} ℤ G₀} {B : TopRep.{u} ℤ G₁} {C : TopRep.{u} ℤ G₂}
    (r : G₁ →ₜ* G₀) (s : G₂ →ₜ* G₁) (t : G₂ →ₜ* G₀)
    (f : TopRep.res r.toMonoidHom A ⟶ B) (g : TopRep.res s.toMonoidHom B ⟶ C)
    (q : TopRep.res t.toMonoidHom A ⟶ C)
    (hGroup : ∀ z, r (s z) = t z) (hCoeff : ∀ a : A, g (f a) = q a)
    (n : ℕ) (x : continuousCohomology n A) :
    (map s g n).hom.toLinearMap.toAddMonoidHom
      ((map r f n).hom.toLinearMap.toAddMonoidHom x) =
      (map t q n).hom.toLinearMap.toAddMonoidHom x :=
  map_comp_eq_apply r s t f g q hGroup hCoeff n x

private def embeddedUpperMuInclusionH2 (n : ℕ) :
    continuousCohomology 2 (separableMuTopRep E n) →+ Br E :=
  (map (X := separableMuTopRep E n) (Y := unitsRep E)
    (ContinuousMonoidHom.id G') (separableMuInclusion E n) 2).hom.toLinearMap.toAddMonoidHom

omit [FiniteDimensional K ↥E] in
private theorem embeddedUpperMuInclusionH2_apply (n : ℕ)
    (x : continuousCohomology 2 (separableMuTopRep E n)) :
    separableMuH2ToBr E n x = embeddedUpperMuInclusionH2 K E n x :=
  separableMuH2ToBr_apply E n x

private def embeddedKummerCompositeCoeff (n : ℕ) :
    TopRep.res (embeddedAbsoluteRestrictionInverseHom K E j).toMonoidHom (separableMuTopRep E n) ⟶
      R (unitsRep K) :=
  (TopRep.resFunctor (embeddedAbsoluteRestrictionInverseHom K E j).toMonoidHom).map
    (separableMuInclusion E n) ≫ embeddedUnitsTransport K E j

private def embeddedKummerCompositeH2 (n : ℕ) :
    continuousCohomology 2 (separableMuTopRep E n) →+
      continuousCohomology 2 (R (unitsRep K)) :=
  let f := map (X := separableMuTopRep E n) (Y := R (unitsRep K))
    (embeddedAbsoluteRestrictionInverseHom K E j) (embeddedKummerCompositeCoeff K E j n) 2
  f.hom.toLinearMap.toAddMonoidHom

private theorem embeddedKummerCompositeH2_viaUnits (n : ℕ)
    (x : continuousCohomology 2 (separableMuTopRep E n)) :
    embeddedUnitsCohomologyTransport K E j (embeddedUpperMuInclusionH2 K E n x) =
      embeddedKummerCompositeH2 K E j n x := by
  let A := separableMuTopRep E n
  let B := unitsRep E
  let C := R (unitsRep K)
  let e : I →ₜ* G' := embeddedAbsoluteRestrictionInverseHom K E j
  let i : A ⟶ B := separableMuInclusion E n
  let g : TopRep.res e.toMonoidHom B ⟶ C := embeddedUnitsTransport K E j
  let q : TopRep.res e.toMonoidHom A ⟶ C := embeddedKummerCompositeCoeff K E j n
  have hq (a : A) : g (i a) = q a :=
    (ConcreteCategory.comp_apply ((TopRep.resFunctor e.toMonoidHom).map i) g a).symm
  exact cohomology_addHom_comp_apply (A := A) (B := B) (C := C)
    (ContinuousMonoidHom.id G') e e i g q (fun _ => rfl) hq 2 x

private theorem embeddedKummerCompositeH2_viaRoots (n : ℕ)
    (x : continuousCohomology 2 (separableMuTopRep E n)) :
    embeddedMuInclusionH2 K E n (embeddedMuCohomologyTransport K E j n x) =
      embeddedKummerCompositeH2 K E j n x := by
  let A := separableMuTopRep E n
  let B := R (separableMuTopRep K n)
  let C := R (unitsRep K)
  let e : I →ₜ* G' := embeddedAbsoluteRestrictionInverseHom K E j
  let f : TopRep.res e.toMonoidHom A ⟶ B := embeddedMuTransport K E j n
  let g : B ⟶ C := (TopRep.resFunctor (I).subtype).map (separableMuInclusion K n)
  let q : TopRep.res e.toMonoidHom A ⟶ C := embeddedKummerCompositeCoeff K E j n
  let i := separableMuInclusion E n
  let t := embeddedUnitsTransport K E j
  have hq (a : A) : g (f a) = q a :=
    (embeddedMuTransport_val K E j n a).trans
      (ConcreteCategory.comp_apply ((TopRep.resFunctor e.toMonoidHom).map i) t a).symm
  exact cohomology_addHom_comp_apply (A := A) (B := B) (C := C)
    e (ContinuousMonoidHom.id I) e f g q (fun _ => rfl) hq 2 x


private theorem embeddedKummerToUnits_natural (n : ℕ)
    (x : continuousCohomology 2 (separableMuTopRep E n)) :
    embeddedUnitsCohomologyTransport K E j (separableMuH2ToBr E n x) =
      embeddedMuInclusionH2 K E n (embeddedMuCohomologyTransport K E j n x) := by
  exact (congrArg (embeddedUnitsCohomologyTransport K E j)
    (embeddedUpperMuInclusionH2_apply K E n x)).trans
      ((embeddedKummerCompositeH2_viaUnits K E j n x).trans
        (embeddedKummerCompositeH2_viaRoots K E j n x).symm)


variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

private theorem localBrauerInvariant_corestrict_embeddedUnits (x : Br E) :
    localBrauerInvariant K (corestrict (unitsRep K) H 2
      (embeddedUnitsCohomologyTransport K E j x)) = localBrauerInvariant E x :=
  localBrauerInvariant_embeddedCorestriction K E j x

private theorem localBrauerInvariant_corestrict_embeddedMu (n : ℕ)
    (x : continuousCohomology 2 (separableMuTopRep E n)) :
    localBrauerInvariant K (corestrict (unitsRep K) H 2
      (embeddedMuInclusionH2 K E n (embeddedMuCohomologyTransport K E j n x))) =
    localBrauerInvariant E (separableMuH2ToBr E n x) := by
  rw [← embeddedKummerToUnits_natural K E j n x]
  exact localBrauerInvariant_corestrict_embeddedUnits K E j (separableMuH2ToBr E n x)

/-- The trace after the actual open-subgroup corestriction is the canonical
upper Kummer trace, using the same original comparison of units. -/
theorem localKummerTrace_embeddedCorestriction (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hnE : ((n : ℕ) : E) ≠ 0) (x : continuousCohomology 2 (separableMuTopRep E n)) :
    localKummerTrace K n hn (corestrict (separableMuTopRep K n) H 2
      (embeddedMuCohomologyTransport K E j n x)) =
      localKummerTrace E n hnE x := by
  apply zmodToRationalCircle_injective n n.pos
  rw [zmodToRationalCircle_localKummerTrace, zmodToRationalCircle_localKummerTrace,
    separableMuH2ToBr_apply K]
  rw [← corestrict_map_coeff H (separableMuTopRep K n) (separableMuInclusion K n)]
  change localBrauerInvariant K (corestrict (unitsRep K) H 2
      (embeddedMuInclusionH2 K E n (embeddedMuCohomologyTransport K E j n x))) =
    localBrauerInvariant E (separableMuH2ToBr E n x)
  exact localBrauerInvariant_corestrict_embeddedMu K E j n x

end ClassFieldTheory.Brauer
