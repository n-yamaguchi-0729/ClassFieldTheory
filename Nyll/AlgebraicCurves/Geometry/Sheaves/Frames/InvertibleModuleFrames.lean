/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Nyll.SchemeTheory.Modules.Frames.FrameFromTrivialization
public import Mathlib.Util.WithWeakNamespace
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Modules.PresheafInternalHom
public import Nyll.SchemeTheory.Modules.Tensor.SheafificationMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.Modules.Frames.Frames

/-!
# Frames near a point of an invertible module

An invertible module admits a section that is a frame on a neighbourhood of each point,
obtained from a local trivialization.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_isFrameOn

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory.Limits

noncomputable section

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

namespace FrameBridge

open Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- A compatible family of generators whose scalar multiplication maps trivialize a module
    presheaf below an object. -/
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

/-- The identity map of ring sheaves describing restriction to the scheme associated to an open
    subset. -/
noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictRingCatSheafHom U

/-- Restriction of module sheaves to an open subset, expressed as a sheaf pushforward. -/
noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor' U

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'_eq U

/-- The natural isomorphism identifying open restriction with pullback along its inclusion. -/
noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'IsoPullback U

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.image_preimage_of_le (U := U) h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- The local generator obtained by applying the inverse trivialization to the unit section. -/
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

/-- The compatible family of local generators supplied by a trivialization of the restricted
    module sheaf. -/
noncomputable def trivializationBelow : TrivializationBelow L.val (op U) :=
  _root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.trivializationBelow L e

end

end FrameBridge

namespace IsInvertible
open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
end IsInvertible
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
open FrameBridge in
theorem IsInvertible.exists_isFrameOn' {X : Scheme.{u}} {M : X.Modules} (hM :
    Scheme.Modules.IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ IsFrameOn s U :=by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  obtain ⟨s, hs⟩ := _root_.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit
    U eU
  exact ⟨U, s, hxU, hs⟩

end AlgebraicGeometry.Scheme.Modules

end

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry Scheme_Modules_IsInvertible_exists_isFrameOn.AlgebraicGeometry
    _root_.AlgebraicGeometry.Scheme.Modules
    Scheme_Modules_IsInvertible_exists_isFrameOn.AlgebraicGeometry.Scheme.Modules in
with_weak_namespace Scheme_Modules_IsInvertible_exists_isFrameOn
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn {X :
    AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn' hM x
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_isFrameOn
end ProofImplementation
