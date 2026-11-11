/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitExact
public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitInvariants
public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitTopology
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Functorial geometric Galois sections

Actual sheaf morphisms induce equivariant maps on geometric sections.
The degree-zero comparison with actual global sections is natural in
the coefficient sheaf.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- Actual coefficient maps commute with the geometric absolute Galois action. -/
theorem finiteGaloisSectionColimitAction_naturality
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) (σ : Gal(AlgebraicClosure K/K)) :
    (finiteGaloisSectionColimitAction K F σ).asIso.hom ≫
        (finiteGaloisSectionColimitFunctor K).map η =
      (finiteGaloisSectionColimitFunctor K).map η ≫
        (finiteGaloisSectionColimitAction K G σ).asIso.hom := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨E, s, rfl⟩ := finiteGaloisSectionColimit_exists_stage K F x
  let a := (finiteGaloisSectionColimitFunctor K).map η
  let e := η.hom.app (op (finiteGaloisEtaleObject K E))
  let τ := AlgEquiv.restrictNormalHom E σ
  change a ((finiteGaloisSectionColimitAction K F σ).asIso.hom
      (finiteGaloisSectionColimitι K F E s)) =
    (finiteGaloisSectionColimitAction K G σ).asIso.hom
      (a (finiteGaloisSectionColimitι K F E s))
  have hm (t : F.obj.obj (op (finiteGaloisEtaleObject K E))) :
      a (finiteGaloisSectionColimitι K F E t) =
        finiteGaloisSectionColimitι K G E (e t) :=
    ConcreteCategory.congr_hom (finiteGaloisSectionColimitFunctor_map_ι K η E) t
  have hf : (finiteGaloisSectionColimitAction K F σ).asIso.hom
      (finiteGaloisSectionColimitι K F E s) =
        finiteGaloisSectionColimitι K F E ((fieldGaloisSheafAction K E F τ).asIso.hom s) :=
    ConcreteCategory.congr_hom (finiteGaloisSectionColimitAction_ι K F σ E) s
  have hg : (finiteGaloisSectionColimitAction K G σ).asIso.hom
      (finiteGaloisSectionColimitι K G E (e s)) =
        finiteGaloisSectionColimitι K G E
          ((fieldGaloisSheafAction K E G τ).asIso.hom (e s)) :=
    ConcreteCategory.congr_hom (finiteGaloisSectionColimitAction_ι K G σ E) (e s)
  have he : e ((fieldGaloisSheafAction K E F τ).asIso.hom s) =
      (fieldGaloisSheafAction K E G τ).asIso.hom (e s) :=
    ConcreteCategory.congr_hom (fieldGaloisSheafAction_naturality K E η τ) s
  exact (congrArg a hf).trans ((hm _).trans
    ((congrArg (finiteGaloisSectionColimitι K G E) he).trans
      (hg.symm.trans
        (congrArg (fun y => (finiteGaloisSectionColimitAction K G σ).asIso.hom y) (hm s).symm))))

/-- The actual coefficient map as an equivariant linear map of geometric sections. -/
def finiteGaloisSectionColimitRepMap
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) :
    finiteGaloisSectionColimitRep K F ⟶ finiteGaloisSectionColimitRep K G :=
  Rep.ofHom
    ⟨((finiteGaloisSectionColimitFunctor K).map η).hom.toIntLinearMap, fun σ => by
      apply LinearMap.ext
      intro x
      exact ConcreteCategory.congr_hom
        (finiteGaloisSectionColimitAction_naturality K η σ) x⟩

/-- The actual geometric-section functor with its absolute Galois action. -/
def finiteGaloisSectionColimitRepFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      Rep.{u} ℤ Gal(AlgebraicClosure K/K) where
  obj := finiteGaloisSectionColimitRep K
  map := finiteGaloisSectionColimitRepMap K
  map_id F := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((finiteGaloisSectionColimitFunctor K).map_id F) x
  map_comp η θ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((finiteGaloisSectionColimitFunctor K).map_comp η θ) x

/-- The geometric-section representation functor is additive. -/
instance finiteGaloisSectionColimitRepFunctor_additive :
    (finiteGaloisSectionColimitRepFunctor K).Additive where
  map_add := by
    intro F G η θ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((finiteGaloisSectionColimitFunctor K).map_add (f := η) (g := θ)) x

/-- Base restriction into actual geometric sections respects coefficient morphisms. -/
theorem finiteGaloisBaseToColimit_naturality
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) :
    finiteGaloisBaseToColimit K F ≫ (finiteGaloisSectionColimitFunctor K).map η =
      η.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) ≫
        finiteGaloisBaseToColimit K G := by
  apply ConcreteCategory.hom_ext
  intro s
  let E : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⊥
  let b := finiteEtaleCoverBaseMap (Spec (.of K))
    (AlgebraicGeometry.FiniteEtale.mk (ξ K E))
  have hm := ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitFunctor_map_ι K η E) (F.obj.map b.op s)
  have hn := ConcreteCategory.congr_hom (η.hom.naturality b.op) s
  exact hm.trans (congrArg (finiteGaloisSectionColimitι K G E) hn)

/-- Actual global sections are naturally the absolute Galois invariant geometric sections. -/
def finiteGaloisBaseInvariantsNatIso :
    (sheafToPresheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation (Spec (.of K)).Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) ≅
    (finiteGaloisSectionColimitRepFunctor K ⋙
      Rep.invariantsFunctor ℤ Gal(AlgebraicClosure K/K) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun F => (finiteGaloisBaseInvariantsAddEquiv K F).toAddCommGrpIso)
    (fun η => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      exact (ConcreteCategory.congr_hom (finiteGaloisBaseToColimit_naturality K η) x).symm)

end EtaleCohomology
