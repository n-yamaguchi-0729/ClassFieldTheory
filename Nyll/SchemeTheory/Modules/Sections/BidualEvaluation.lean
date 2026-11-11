/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The canonical `ZeroSchemeCanonMC.toBidual` construction is moved from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and new evaluation laws: Copyright (c) 2026 Naganori Yamaguchi
(https://github.com/n-yamaguchi-0729).
Authors of local additions: Naganori Yamaguchi (assisted by OpenAI Codex).
-/

module

public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeDual
public import Nyll.SchemeTheory.Modules.LocalMorphisms
public import Nyll.SchemeTheory.Modules.Tensor.TensorSectionBraiding
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The canonical bidual map on actual module sheaves

The existing braided evaluation construction is placed with the module
foundations. Evaluation on original local sections proves naturality and
the splitting of the bidual map of a dual. These statements use the native
internal Hom and its existing evaluation, without another dual model.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.ZeroSchemeCanonMC

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The canonical map to the internal-Hom bidual, obtained by currying the
braided evaluation map. -/
def toBidual (M : C) : M ⟶ (ihom ((ihom M).obj (𝟙_ C))).obj (𝟙_ C) :=
  MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))

end Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.ZeroSchemeCanonMC
end AlgebraicCurves.Geometry.Sheaves.Proofs

open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The canonical bidual map sends a section to evaluation at that section. -/
theorem toBidual_eval (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (φ : Γ(dual M, U)) :
    ihomEval (dual M) (𝟙_ X.Modules) U φ ((ZeroSchemeCanonMC.toBidual M).app U m) =
      ihomEval M (𝟙_ X.Modules) U m φ := by
  rw [ZeroSchemeCanonMC.toBidual, ihomEval_curry_app]
  change ((ihom.ev M).app (𝟙_ X.Modules)).app U
    ((β_ (dual M) M).hom.app U (tensorSections φ m)) = _
  rw [braiding_hom_app_tensorSections, ihom_ev_app_tensorSections]

/-- Bidual evaluation is natural for actual module-sheaf morphisms. -/
theorem toBidual_naturality {M N : X.Modules} (f : M ⟶ N) :
    f ≫ ZeroSchemeCanonMC.toBidual N =
      ZeroSchemeCanonMC.toBidual M ≫
        (MonoidalClosed.pre ((MonoidalClosed.pre f).app (𝟙_ X.Modules))).app
          (𝟙_ X.Modules) := by
  apply ihom_hom_ext
  intro U φ m
  change ihomEval (dual N) (𝟙_ X.Modules) U φ
    ((ZeroSchemeCanonMC.toBidual N).app U (f.app U m)) =
    ihomEval (dual N) (𝟙_ X.Modules) U φ
      (((MonoidalClosed.pre ((MonoidalClosed.pre f).app (𝟙_ X.Modules))).app
        (𝟙_ X.Modules)).app U ((ZeroSchemeCanonMC.toBidual M).app U m))
  rw [ihomEval_pre_app, toBidual_eval, toBidual_eval, ihomEval_pre_app]

/-- Precomposition with the original bidual map is a left inverse to the
bidual map of a dual. In particular this is a genuine splitting. -/
theorem toBidual_dual_comp_pre (M : X.Modules) :
    ZeroSchemeCanonMC.toBidual (dual M) ≫
      (MonoidalClosed.pre (ZeroSchemeCanonMC.toBidual M)).app (𝟙_ X.Modules) =
        𝟙 (dual M) := by
  apply ihom_hom_ext
  intro U m φ
  change ihomEval M (𝟙_ X.Modules) U m
    (((MonoidalClosed.pre (ZeroSchemeCanonMC.toBidual M)).app (𝟙_ X.Modules)).app U
      ((ZeroSchemeCanonMC.toBidual (dual M)).app U φ)) =
    ihomEval M (𝟙_ X.Modules) U m φ
  rw [ihomEval_pre_app, toBidual_eval, toBidual_eval]

/-- The original bidual map is bijective on every finite trivializing
open: under actual evaluation of dual sections it is the usual module
bidual evaluation. -/
theorem toBidual_app_bijective_of_isFiniteFreeOn
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    Function.Bijective ((ZeroSchemeCanonMC.toBidual M).app U) := by
  have : Module.Free Γ(X, U) Γ(M, U) := IsFiniteFreeOn.moduleFree M hU
  have : Module.Finite Γ(X, U) Γ(M, U) := IsFiniteFreeOn.moduleFinite M hU
  have : Module.IsReflexive Γ(X, U) Γ(M, U) :=
    Module.IsReflexive.of_finite_of_free Γ(X, U) Γ(M, U)
  let E := dualSectionsEquivOfIsFiniteFreeOn M hU
  let D := dualSectionsEquivOfIsFiniteFreeOn (dual M) hU.dual
  let e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(dual (dual M), U) :=
    ((Module.evalEquiv Γ(X, U) Γ(M, U)).trans E.dualMap).trans D.symm
  have he (m : Γ(M, U)) : e m = (ZeroSchemeCanonMC.toBidual M).app U m := by
    apply D.injective
    change D (D.symm (E.dualMap (Module.evalEquiv Γ(X, U) Γ(M, U) m))) = _
    rw [D.apply_symm_apply]
    apply LinearMap.ext
    intro φ
    change E φ m = ihomEval (dual M) (𝟙_ X.Modules) U φ
      ((ZeroSchemeCanonMC.toBidual M).app U m)
    rw [toBidual_eval]
    rfl
  constructor
  · intro m n h
    apply e.injective
    rw [he, he, h]
  · intro t
    obtain ⟨m, hm⟩ := e.surjective t
    exact ⟨m, (he m).symm.trans hm⟩

/-- Every finite locally free module is reflexive through its actual
canonical internal-Hom bidual evaluation. The finite rank may vary. -/
theorem isIso_toBidual_of_finiteFreeLocus_eq_top
    {X : Scheme.{u}} (M : X.Modules) (hM : finiteFreeLocus M = ⊤) :
    IsIso (ZeroSchemeCanonMC.toBidual M) := by
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsFiniteFreeOn M U := by
    apply (mem_finiteFreeLocus_iff M x).mp
    rw [hM]
    trivial
  choose U hxU hU using hlocal
  apply Hom.isIso_of_isIso_app_of_iSup_eq_top (ZeroSchemeCanonMC.toBidual M) U
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · intro x V hV
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (toBidual_app_bijective_of_isFiniteFreeOn M (IsFiniteFreeOn.mono M (hU x) hV))

/-- The original bidual map restricts to an isomorphism on every open
contained in the finite locally free locus. No comparison with a separately
constructed restricted dual is assumed. -/
theorem isIso_restrict_toBidual_of_le_finiteFreeLocus
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hU : U ≤ finiteFreeLocus M) :
    IsIso ((restrictFunctor U.ι).map (ZeroSchemeCanonMC.toBidual M)) := by
  have hlocal (x : U) : ∃ V : X.Opens, U.ι x ∈ V ∧ IsFiniteFreeOn M V :=
    (mem_finiteFreeLocus_iff M (U.ι x)).mp (hU x.property)
  choose V hxV hV using hlocal
  let W (x : U) : U.toScheme.Opens := U.ι ⁻¹ᵁ V x
  apply Hom.isIso_of_isIso_app_of_iSup_eq_top
    ((restrictFunctor U.ι).map (ZeroSchemeCanonMC.toBidual M)) W
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · intro x Z hZ
    have hZV : U.ι ''ᵁ Z ≤ V x :=
      (U.ι.image_mono hZ).trans (U.ι.image_preimage_le (V x))
    change IsIso ((ZeroSchemeCanonMC.toBidual M).app (U.ι ''ᵁ Z))
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (toBidual_app_bijective_of_isFiniteFreeOn M (IsFiniteFreeOn.mono M (hV x) hZV))


/-- Reflexivity through canonical bidual evaluation is invariant under an
actual module-sheaf isomorphism. -/
theorem isIso_toBidual_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [IsIso (ZeroSchemeCanonMC.toBidual M)] :
    IsIso (ZeroSchemeCanonMC.toBidual N) := by
  let d : dual N ≅ dual M :=
    ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.op).app (𝟙_ X.Modules)
  let dd : dual (dual M) ≅ dual (dual N) :=
    ((MonoidalClosed.internalHom (C := X.Modules)).mapIso d.op).app (𝟙_ X.Modules)
  have h : e.hom ≫ ZeroSchemeCanonMC.toBidual N =
      ZeroSchemeCanonMC.toBidual M ≫ dd.hom := toBidual_naturality e.hom
  have : IsIso (e.hom ≫ ZeroSchemeCanonMC.toBidual N) :=
    h.symm ▸ inferInstanceAs (IsIso (ZeroSchemeCanonMC.toBidual M ≫ dd.hom))
  exact IsIso.of_isIso_comp_left e.hom (ZeroSchemeCanonMC.toBidual N)


end AlgebraicGeometry.Scheme.Modules
