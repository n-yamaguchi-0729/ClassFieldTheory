/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Frames.Frames

/-!
# Frames obtained from a pullback trivialization

A trivialization on an open subscheme gives compatible local generators and a section
that is a frame on that open.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits

noncomputable section

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

namespace FrameBridge

open Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Compatible generators trivializing the presheaf on objects reached from `X₀`. -/
abbrev TrivializationBelow (X₀ : Cᵒᵖ) :=
  _root_.PresheafOfModules.FrameBridge.TrivializationBelow F X₀

namespace TrivializationBelow

export _root_.PresheafOfModules.FrameBridge.TrivializationBelow (mk gen compat bij)

end TrivializationBelow

end FrameBridge

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace FrameBridge

open TopologicalSpace Opposite _root_.PresheafOfModules.FrameBridge

variable {X : Scheme.{u}}

variable (U : X.Opens)

/-- The ring-sheaf morphism used to restrict module sheaves to the open subscheme. -/
noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictRingCatSheafHom U

/-- Restriction expressed as pushforward along the inclusion of the open indexing categories. -/
noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor' U

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'_eq U

/-- The canonical comparison between the restriction functor and pullback to the open. -/
noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'IsoPullback U

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.image_preimage_of_le (U := U) h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- The generator obtained by transporting one through the inverse trivialization. -/
noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀ L e W

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_spec L e W b

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W)) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_bijective L e W

lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_map L e i

omit e in
lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • (show Γ(L, A) from t))) :
    Function.Bijective (fun a : Γ(X, B) =>
      a • (show Γ(L, B) from L.val.map (eqToHom q.symm : B ⟶ A).op t)) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.bijective_smul_map_eqToHom L q t h

/-- The compatible generators on opens contained in the trivializing open `U`. -/
noncomputable def trivializationBelow : TrivializationBelow L.val (op U) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.trivializationBelow L e

end

end FrameBridge

theorem exists_isFrameOn_of_pullback_iso_unit {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), IsFrameOn s U := by
  let e : (_root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor' U).obj M ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (_root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'IsoPullback U).app M ≪≫ eU
  let D := _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.trivializationBelow M e
  refine ⟨D.gen (𝟙 (Opposite.op U)), ?_⟩
  intro W hWU _
  have hc : M.presheaf.map (homOfLE hWU).op (D.gen (𝟙 (Opposite.op U))) = D.gen (homOfLE hWU).op :=
      by
    have h := D.compat (𝟙 (Opposite.op U)) (homOfLE hWU).op
    rw [Category.id_comp] at h
    exact h
  simp only [hc]
  exact D.bij (homOfLE hWU).op

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry in
open Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), Scheme.Modules.IsFrameOn s U :=
  Modules.exists_isFrameOn_of_pullback_iso_unit U eU
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
end ProofImplementation
