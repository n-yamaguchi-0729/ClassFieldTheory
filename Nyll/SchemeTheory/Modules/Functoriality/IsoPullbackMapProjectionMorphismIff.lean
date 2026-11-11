/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.PresheafInternalHom
public import Nyll.SchemeTheory.Modules.Tensor.SheafificationMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PresheafPullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionSheafification
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
public import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorObjIsoHomAppPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.ProjectionMorphism
public import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeIsomorphism
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
public import Mathlib.Util.WithWeakNamespace
/-!
Compatibility of the projection morphism with restriction and pullback on an open subscheme.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_pullback_map_projectionMorphism_iff

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct
open _root_.CategoryTheory.Functor.LaxMonoidal
open _root_.CategoryTheory.Functor.OplaxMonoidal

local instance projectionPresheafSectionsModule {Z : Scheme.{u}}
    (P : Z.PresheafOfModules) (U : Z.Opens) :
    Module Γ(Z, U) (P.obj (op U)) := (P.obj (op U)).isModule

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme

-- Preserve the proof-namespace names through the existing comparison owner.
export Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection.AlgebraicGeometry.Scheme
  (Modules.PullbackTensorSections.adj₀
    Modules.PullbackTensorSections.e
    Modules.PullbackTensorSections.pb₀Section
    Modules.PullbackTensorSections.shUnit
    Modules.PullbackTensorSections.sheafify_map_app_shUnit
    Modules.PullbackTensorSections.counit_app_shUnit
    Modules.PullbackTensorSections.homEquiv_symm_app_pb₀Section
    Modules.PullbackTensorSections.e_hom_app_pullbackLocalSection
    Modules.PullbackTensorSections.e_inv_app_shUnit
    Modules.PullbackTensorSections.pb₀_δ_eq
    Modules.PullbackTensorSections.pb₀_δ_app_pb₀Section_tmul
    Modules.PullbackTensorSections.sheafify_δ_app_shUnit_tmul
    Modules.PullbackTensorSections.e_hom_app_tensor_comp_δ
    Modules.PullbackTensorSections.cmpIso
    Modules.PullbackTensorSections.cmpIso_hom
    Modules.PullbackTensorSections.tensorSections_eq
    Modules.PullbackTensorSections.δ_sheafify_comp_pullback_eq
    Modules.PullbackTensorSections.pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections)

namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace PullbackTensorSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance : (PresheafOfModules.pushforward.{u}
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom.hom).IsRightAdjoint :=
  (PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).isRightAdjoint

local instance : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (Modules.pullbackPushforwardAdjunction f).isRightAdjoint

open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

/-- The underlying presheaf functor for sheaves of modules on a scheme. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.ι (Z : Scheme.{u})
    : Z.Modules ⥤ Z.PresheafOfModules :=
  SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property
open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

open _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

local instance : (pf f).LaxMonoidal :=
  PresheafOfModules.pushforward_laxMonoidal
    (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

lemma pf_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pf f)).app (op V) g = (f.app V (show Γ(Y, V) from g) :
      ((pf f).obj (𝟙_ X.PresheafOfModules)).obj (op V)) := by
  let : (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)).LaxMonoidal :=
    PresheafOfModules.restrictScalars_laxMonoidal
      (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) (S := Y.sheaf.obj) f.c
  change (ε (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)) ≫
    (PresheafOfModules.restrictScalars
      (PresheafOfModules.ringCatHom (R := (TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj)
        f.c)).map
        (ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base)
          X.sheaf.obj))).app
      (op V) g = _
  erw [show ε (PresheafOfModules.pushforward₀OfCommRingCat (TopologicalSpace.Opens.map f.base)
    X.sheaf.obj)
      = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  rfl

lemma pb₀_η_app_pb₀Section (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g)
      = (f.app V (show Γ(Y, V) from g) : (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V))) := by
  have h : η (pullback₀ f) = ((adj₀ f).homEquiv _ _).symm (ε (pf f)) :=
    Adjunction.leftAdjointOplaxMonoidal_η (adj₀ f)
  rw [h]
  erw [homEquiv_symm_app_pb₀Section f (ε (pf f)) V g]
  exact pf_ε_app f V g

lemma pb₀_ε_app (V : Y.Opens) (g : (𝟙_ Y.PresheafOfModules).obj (op V)) :
    (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (f.app V (show Γ(Y, V) from g) : (𝟙_
      X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)))
      = pb₀Section f (𝟙_ Y.PresheafOfModules) V g := by
  have h1 := pb₀_η_app_pb₀Section f V g
  have h2 := congr($(Functor.Monoidal.η_ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
    (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
  change (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      ((η (pullback₀ f)).app (op (f ⁻¹ᵁ V)) (pb₀Section f (𝟙_ Y.PresheafOfModules) V g))
    = pb₀Section f (𝟙_ Y.PresheafOfModules) V g at h2
  rw [h1] at h2
  exact h2

lemma sheafify_ε_app {Z : Scheme.{u}} (W : Z.Opens) (c : Γ(𝟙_ Z.Modules, W)) :
    Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W c = shUnit (𝟙_ Z.PresheafOfModules) W c := by
  have h1 : Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W
    c) = c :=
    counit_app_shUnit (𝟙_ Z.Modules) W c
  have h2 := congr($(Functor.Monoidal.η_ε (Modules.sheafify Z)).app W (shUnit (𝟙_
    Z.PresheafOfModules) W c))
  change Scheme.Modules.Hom.app (ε (Modules.sheafify Z)) W
      (Scheme.Modules.Hom.app (η (Modules.sheafify Z)) W (shUnit (𝟙_ Z.PresheafOfModules) W c))
    = shUnit (𝟙_ Z.PresheafOfModules) W c at h2
  rw [h1] at h2
  exact h2


lemma pullback_ε_app_unitSection (V : Y.Opens) :
    Scheme.Modules.Hom.app (ε (Modules.pullback f)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V))
      = pullbackLocalSection f (Modules.unitSection V) := by
  have : MorphismProperty.ContainsIdentities (C := Y.PresheafOfModules)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
    MorphismProperty.ContainsIdentities.inverseImage
      (P := (Opens.grothendieckTopology Y).W (A := AddCommGrpCat.{u}))
      (PresheafOfModules.toPresheaf (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  let := SheafOfModules.presheafW_isMonoidal
    (J := Opens.grothendieckTopology Y) Y.sheaf.obj Y.ringCatSheaf.property
  have hε := Localization.Monoidal.functorMonoidalOfComp_ε (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  erw [hε, Functor.LaxMonoidal.comp_ε]
  change Scheme.Modules.Hom.app ((Modules.pullback f).map (η (Modules.sheafify Y))) (f ⁻¹ᵁ V)
    (Scheme.Modules.Hom.app ((e f).inv.app (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app (ε (Modules.sheafify X)) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ
          V))))) = _
  rw [sheafify_ε_app]
  have hmap : Scheme.Modules.Hom.app ((Modules.sheafify X).map (ε (pullback₀ f))) (f ⁻¹ᵁ V)
      (shUnit (𝟙_ X.PresheafOfModules) (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)))
      = shUnit ((pullback₀ f).obj (𝟙_ Y.PresheafOfModules)) (f ⁻¹ᵁ V)
          ((ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
            (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ
              V))) :=
    sheafify_map_app_shUnit (ε (pullback₀ f)) (f ⁻¹ᵁ V) _
  have h1 : (ε (pullback₀ f)).app (op (f ⁻¹ᵁ V))
      (show (𝟙_ X.PresheafOfModules).obj (op (f ⁻¹ᵁ V)) from Modules.unitSection (f ⁻¹ᵁ V))
        = pb₀Section f (𝟙_ Y.PresheafOfModules) V (Modules.unitSection V) := by
    erw [← pb₀_ε_app f V (Modules.unitSection V)]
    congr 1
    exact ((f.app V).hom.map_one).symm
  erw [hmap, h1, e_inv_app_shUnit, ← pullbackLocalSection_app]
  congr 1
  exact counit_app_shUnit (𝟙_ Y.Modules) V (Modules.unitSection V)

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (V : Y.Opens) :
    (pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V) (pullbackLocalSection f (Modules.unitSection V))
      = Modules.unitSection (f ⁻¹ᵁ V) := by
  rw [← pullback_ε_app_unitSection]
  change Scheme.Modules.Hom.app (ε (Modules.pullback f) ≫ (Functor.Monoidal.εIso
    (Modules.pullback f)).inv)
    (f ⁻¹ᵁ V) (Modules.unitSection (f ⁻¹ᵁ V)) = _
  rw [Functor.Monoidal.εIso_inv, Functor.Monoidal.ε_η]
  rfl

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' (V : Y.Opens) (g : Γ(𝟙_
    Y.Modules, V)) :
    ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f g) =
      (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
  have hg : (show Γ(Y, V) from g) • Modules.unitSection V = g := by
    change (show Γ(Y, V) from g) * 1 = (show Γ(Y, V) from g)
    exact mul_one _
  have key : ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V))
      (pullbackLocalSection f ((show Γ(Y, V) from g) • Modules.unitSection V)) =
        (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ V) from f.app V (show Γ(Y, V) from g)) := by
    rw [pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
      pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
    change f.app V (show Γ(Y, V) from g) * 1 = _
    rw [mul_one]
  rw [hg] at key
  exact key

end PullbackTensorSections

end AlgebraicGeometry.Scheme.Modules

open TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Ws31Restrict

variable {W X Y Z : Scheme.{u}}

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
with_weak_namespace AlgebraicGeometry.Scheme
open Modules in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isIso_pullback_map_projectionMorphism_iff.Ws31Restrict
private theorem pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections (f : X ⟶ Y) (L
    M : Y.Modules)
    (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f (tensorSections s t))
      = tensorSections (pullbackLocalSection f s) (pullbackLocalSection f t) :=
  _root_.AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection
    f s t
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
with_weak_namespace AlgebraicGeometry.Scheme
open Modules in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isIso_pullback_map_projectionMorphism_iff.Ws31Restrict
theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection (f : X ⟶ Y) (V : Y.Opens) (g :
    Γ(𝟙_ Y.Modules, V)) :
    ((pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ V)) (pullbackLocalSection f g)
      = (f.app V (g : Γ(Y, V)) : Γ(𝟙_ X.Modules, f ⁻¹ᵁ V)) :=
  PullbackTensorSections.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection'
    f V g

theorem projectionMorphism_app_tensorSections (i : Z ⟶ X) (F : X.Modules) (V : X.Opens)
    (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s : Γ(F, V)) :
    (projectionMorphism i F).app V (tensorSections a s)
      = (((show Γ(Z, i ⁻¹ᵁ V) from a) • pullbackLocalSection i s : Γ((Scheme.Modules.pullback
        i).obj F, i ⁻¹ᵁ V))
          : Γ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F), V)) := by
  rw [projectionMorphism_def, Adjunction.homEquiv_unit]
  change (projectionMorphismMate i F).app (i ⁻¹ᵁ V) (pullbackLocalSection i (tensorSections a
    s)) = _
  rw [projectionMorphismMate_def]
  change (λ_ ((Scheme.Modules.pullback i).obj F)).hom.app _
      ((((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules)) ▷
          (Scheme.Modules.pullback i).obj F).app _
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback i)
            ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv.app _
          (pullbackLocalSection i (tensorSections a s)))) = _
  have hB1 : (Functor.Monoidal.μIso (Scheme.Modules.pullback i)
        ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv.app (i ⁻¹ᵁ V)
        (pullbackLocalSection i (tensorSections a s))
      = tensorSections (pullbackLocalSection i a) (pullbackLocalSection i s) :=
    pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections i _ F V a s
  rw [hB1, whiskerRight_app_tensorSections, counit_app_pullbackLocalSection]
  exact leftUnitor_hom_app_tensorSections (X := Z)
    (N := (Scheme.Modules.pullback i).obj F) (U := i ⁻¹ᵁ V)
    (show Γ(Z, i ⁻¹ᵁ V) from a) (pullbackLocalSection i s)

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (k : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map k.op m) = N.presheaf.map k.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val k.op m

theorem pullbackComp_hom_app_app_pullbackLocalSection (f : W ⟶ X) (g : X ⟶ Y) (L : Y.Modules) (V
    : Y.Opens)
    (s : Γ(L, V)) :
    (((pullbackComp f g).hom.app L).app (f ⁻¹ᵁ g ⁻¹ᵁ V)) (pullbackLocalSection f
      (pullbackLocalSection g s))
      = pullbackLocalSection (f ≫ g) s := by
  have h := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (pullbackComp f g).hom L
  rw [conjugateEquiv_pullbackComp_hom, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun k => Scheme.Modules.Hom.app k V s) h
  exact h'.symm

theorem pullbackCongr_hom_app_app_pullbackLocalSection {f g : X ⟶ Y} (e : f = g) (L : Y.Modules)
    (V : Y.Opens)
    (s : Γ(L, V)) :
    (((pullbackCongr e).hom.app L).app (f ⁻¹ᵁ V)) (pullbackLocalSection f s)
      = ((Scheme.Modules.pullback g).obj L).presheaf.map (eqToHom (by rw [e])).op
        (pullbackLocalSection g s) := by
  subst e
  simp [pullbackCongr]

section main
variable (i : Z ⟶ X) (F : X.Modules) (U : X.Opens)

theorem sq : (i ⁻¹ᵁ U).ι ≫ i = (i ∣_ U) ≫ U.ι := (morphismRestrict_ι i U).symm

theorem preimage_eq (V : X.Opens) : (i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V = (i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq]

theorem isIso_bc (N : Z.Modules) : IsIso (baseChangeHom (sq i U) N) :=
  isIso_baseChangeHom_of_isOpenImmersion (isPullback_morphismRestrict i U).flip N

theorem bc_app_pullbackLocalSection (N : Z.Modules) (V : X.Opens)
    (t : Γ((Scheme.Modules.pushforward i).obj N, V)) :
    (baseChangeHom (sq i U) N).app (U.ι ⁻¹ᵁ V) (pullbackLocalSection U.ι t)
      = ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj N).presheaf.map (eqToHom (preimage_eq i U V)).op
          (pullbackLocalSection (i ⁻¹ᵁ U).ι (t : Γ(N, i ⁻¹ᵁ V))) := by
  have h := unit_app_app_comp_baseChangeHom_app i U.ι (i ∣_ U) (i ⁻¹ᵁ U).ι (sq i U) N V
  exact CategoryTheory.ConcreteCategory.congr_hom h t

/-- The comparison between restricted pullback and pullback after restriction. -/
noncomputable def τIso :
    (Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F) ≅
      (Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F) :=
  (pullbackComp (i ∣_ U) U.ι).app F ≪≫ (pullbackCongr (sq i U).symm).app F ≪≫
    ((pullbackComp (i ⁻¹ᵁ U).ι i).app F).symm

theorem τIso_hom_app_pullbackLocalSection (V : X.Opens) (s : Γ(F, V)) :
    (τIso i F U).hom.app _ (pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s))
      = ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F)).presheaf.map
          (eqToHom (preimage_eq i U V)).op (pullbackLocalSection (i ⁻¹ᵁ U).ι
            (pullbackLocalSection i s)) := by
  have h1 := pullbackComp_hom_app_app_pullbackLocalSection (i ∣_ U) U.ι F V s
  have h2 := pullbackCongr_hom_app_app_pullbackLocalSection (sq i U).symm F V s
  have h3 := pullbackComp_hom_app_app_pullbackLocalSection (i ⁻¹ᵁ U).ι i F V s
  have hid := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k ((i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V))
      ((pullbackComp (i ⁻¹ᵁ U).ι i).hom_inv_id_app F))
    (pullbackLocalSection (i ⁻¹ᵁ U).ι (pullbackLocalSection i s))
  have h3' : ((pullbackComp (i ⁻¹ᵁ U).ι i).inv.app F).app ((i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V)
      (pullbackLocalSection ((i ⁻¹ᵁ U).ι ≫ i) s) = pullbackLocalSection (i ⁻¹ᵁ U).ι
        (pullbackLocalSection i s) := by
    rw [← h3]
    exact hid
  change ((pullbackComp (i ⁻¹ᵁ U).ι i).inv.app F).app _
      (((pullbackCongr (sq i U).symm).hom.app F).app _
        (((pullbackComp (i ∣_ U) U.ι).hom.app F).app _ (pullbackLocalSection (i ∣_ U)
          (pullbackLocalSection U.ι s)))) = _
  rw [h1]
  erw [h2, app_naturality, h3']
  all_goals rfl

/-- The comparison isomorphism for restriction of the projection formula source. -/
noncomputable def βIso :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj F)) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj
        ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)) :=
  haveI := isIso_bc i U ((Scheme.Modules.pullback i).obj F)
  asIso (baseChangeHom (sq i U) ((Scheme.Modules.pullback i).obj F)) ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso (τIso i F U).symm

/-- The base change isomorphism for the pushforward of the unit module. -/
noncomputable def unitBC :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _) :=
  haveI := isIso_bc i U (𝟙_ Z.Modules)
  asIso (baseChangeHom (sq i U) (𝟙_ Z.Modules)) ≪≫
    (Scheme.Modules.pushforward (i ∣_ U)).mapIso (pullbackTensorUnitObjIso (i ⁻¹ᵁ U).ι)

/-- The comparison isomorphism for restriction of the projection formula target. -/
noncomputable def αIso :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ≅
      (Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _) ⊗ (Scheme.Modules.pullback U.ι).obj F :=
  pullbackTensorObjIso U.ι _ F ≪≫ whiskerRightIso (unitBC i U) _

/-- The scalar expression for the projection formula after restriction. -/
noncomputable def nf (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V))
    (s : Γ(F, V)) :
    Γ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F), (i ∣_ U) ⁻¹ᵁ
      U.ι ⁻¹ᵁ V) :=
  (show Γ(↑(i ⁻¹ᵁ U), (i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V) from
      (i ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (preimage_eq i U V)).op
        ((i ⁻¹ᵁ U).ι.app (i ⁻¹ᵁ V) (show Γ(Z, i ⁻¹ᵁ V) from a))) •
    pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s)

theorem key_lhs (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s :
    Γ(F, V)) :
    ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom).app (U.ι ⁻¹ᵁ V)
        (pullbackLocalSection U.ι (tensorSections a s))
      = (nf i F U V a s : Γ((Scheme.Modules.pushforward (i ∣_ U)).obj
          ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)), U.ι
            ⁻¹ᵁ V)) := by
  have := isIso_bc i U ((Scheme.Modules.pullback i).obj F)
  change (τIso i F U).inv.app _ ((baseChangeHom (sq i U) ((Scheme.Modules.pullback i).obj F)).app _
    (((Scheme.Modules.pullback U.ι).map (projectionMorphism i F)).app _ (pullbackLocalSection
      U.ι (tensorSections a s)))) = _
  rw [← pullbackLocalSection_app, projectionMorphism_app_tensorSections]
  erw [bc_app_pullbackLocalSection i U ((Scheme.Modules.pullback i).obj F) V]
  rw [pullbackLocalSection_smul, Scheme.Modules.map_smul, Scheme.Modules.Hom.app_smul]
  have hτ := τIso_hom_app_pullbackLocalSection i F U V s
  have hid := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k ((i ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V)) ((τIso i F
      U).hom_inv_id))
    (pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s))
  have hinv : (τIso i F U).inv.app _
      (((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback i).obj F)).presheaf.map
          (eqToHom (preimage_eq i U V)).op (pullbackLocalSection (i ⁻¹ᵁ U).ι
            (pullbackLocalSection i s)))
      = pullbackLocalSection (i ∣_ U) (pullbackLocalSection U.ι s) := by
    rw [← hτ]
    exact hid
  erw [hinv]
  all_goals rfl

theorem key_rhs (V : X.Opens) (a : Γ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules), V)) (s :
    Γ(F, V)) :
    ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)).app
      (U.ι ⁻¹ᵁ V)
        (pullbackLocalSection U.ι (tensorSections a s))
      = (nf i F U V a s : Γ((Scheme.Modules.pushforward (i ∣_ U)).obj
          ((Scheme.Modules.pullback (i ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj F)), U.ι
            ⁻¹ᵁ V)) := by
  have := isIso_bc i U (𝟙_ Z.Modules)
  change (projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)).app _
    (((unitBC i U).hom ▷ (Scheme.Modules.pullback U.ι).obj F).app _
      ((pullbackTensorObjIso U.ι ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) F).hom.app _
        (pullbackLocalSection U.ι (tensorSections a s)))) = _
  rw [pullbackTensorObjIso_hom_app_pullbackLocalSection_tensorSections,
    whiskerRight_app_tensorSections]
  have hu : (unitBC i U).hom.app (U.ι ⁻¹ᵁ V) (pullbackLocalSection U.ι a)
      = (show Γ((Scheme.Modules.pushforward (i ∣_ U)).obj (𝟙_ _), U.ι ⁻¹ᵁ V) from
          (𝟙_ (↑(i ⁻¹ᵁ U) : Scheme.{u}).Modules).presheaf.map (eqToHom (preimage_eq i U V)).op
            ((show Γ(𝟙_ (↑(i ⁻¹ᵁ U) : Scheme.{u}).Modules, (i ⁻¹ᵁ U).ι ⁻¹ᵁ i ⁻¹ᵁ V) from
              (i ⁻¹ᵁ U).ι.app (i ⁻¹ᵁ V) (show Γ(Z, i ⁻¹ᵁ V) from a)))) := by
    change (pullbackTensorUnitObjIso (i ⁻¹ᵁ U).ι).hom.app _
      ((baseChangeHom (sq i U) (𝟙_ Z.Modules)).app _ (pullbackLocalSection U.ι a)) = _
    erw [bc_app_pullbackLocalSection i U (𝟙_ Z.Modules) V a]
    rw [app_naturality]
    erw [pullbackTensorUnitObjIso_hom_app_pullbackLocalSection]
  rw [hu]
  erw [projectionMorphism_app_tensorSections]
  all_goals rfl

theorem key :
    (Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom
      = (αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _).injective
  apply tensor_hom_ext
  intro V a s
  have e1 := app_pullbackLocalSection U.ι
    ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F U).hom)
      (tensorSections a s)
  have e2 := app_pullbackLocalSection U.ι
    ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F))
      (tensorSections a s)
  rw [key_lhs] at e1
  rw [key_rhs] at e2
  exact e1.symm.trans e2

theorem main :
    IsIso ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F)) ↔
      IsIso (projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) := by
  have hk := key i F U
  constructor
  · intro h
    have e : projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)
        = (αIso i F U).inv ≫ ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso
          i F U).hom) := by
      rw [hk, Iso.inv_hom_id_assoc]
    have h1 : IsIso ((Scheme.Modules.pullback U.ι).map (projectionMorphism i F) ≫ (βIso i F
      U).hom) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_hom _)
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) h1
  · intro h
    have e : (Scheme.Modules.pullback U.ι).map (projectionMorphism i F)
        = ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) ≫
            (βIso i F U).inv := by
      rw [← hk, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h1 : IsIso ((αIso i F U).hom ≫ projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback
      U.ι).obj F)) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) h
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (Iso.isIso_inv _)

end main

end Ws31Restrict

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_pullback_map_projectionMorphism_iff {Z X :
    Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) (U : X.Opens) :
    IsIso ((Scheme.Modules.pullback U.ι).map (Scheme.Modules.projectionMorphism i F)) ↔
      IsIso (Scheme.Modules.projectionMorphism (i ∣_ U) ((Scheme.Modules.pullback U.ι).obj F)) :=
  Ws31Restrict.main i F U

end
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
end ProofImplementation

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
