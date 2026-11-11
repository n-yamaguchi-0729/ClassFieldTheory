/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Nyll.SchemeTheory.RingTheory.PushoutKernel

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Local surjectivity of the ideal-module pullback comparison

The canonical map from a pulled-back ideal module to the inverse-image ideal module
is locally surjective.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective

universe u

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace Algebra
open _root_.Algebra
namespace IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra

theorem lbE_ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  exact _root_.Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hC

end Algebra.IsPushout

namespace CommRingCat
open _root_.CommRingCat
open _root_.CommRingCat

theorem lbE_ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  exact _root_.CommRingCat.ker_eq_map_ker_of_isPushout h hg

end CommRingCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

theorem lbE_ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_top I f


theorem lbE_ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le I f U V hVU

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open Opposite TopologicalSpace

local instance pullbackComparisonRightAdjoint {X X' : Scheme.{u}} (f : X' ⟶ X) :
    (SheafOfModules.pushforward.{u}
      (F := TopologicalSpace.Opens.map f.base)
      (J := _root_.Opens.grothendieckTopology X)
      (K := _root_.Opens.grothendieckTopology X') f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

private lemma
    _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleToPushforwardComapModule_comp_map_moduleι
    {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    I.moduleToPushforwardComapModule f ≫
        (SheafOfModules.pushforward f.toRingCatSheafHom).map
          (kernel.ι (I.comap f).subschemeι.unitToPushforwardUnit) =
      kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit := by
  rw [moduleToPushforwardComapModule]
  erw [Category.assoc]
  erw [PreservesKernel.iso_inv_ι (SheafOfModules.pushforward f.toRingCatSheafHom)
    ((I.comap f).subschemeι.unitToPushforwardUnit)]
  exact kernel.lift_ι ((SheafOfModules.pushforward f.toRingCatSheafHom).map
    ((I.comap f).subschemeι.unitToPushforwardUnit)) _ _

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.unit_comp_map_pullbackModuleComparison
    {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).unit.app
        (I.module : SheafOfModules X.ringCatSheaf) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map (I.pullbackModuleComparison f) =
      I.moduleToPushforwardComapModule f := by
  have h : (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
      (I.pullbackModuleComparison f) = I.moduleToPushforwardComapModule f :=
    Equiv.apply_symm_apply _ _
  exact (Adjunction.homEquiv_unit (adj := SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom) (f := I.pullbackModuleComparison f)).symm.trans h

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

theorem lbE_pullbackModuleComparison_locallySurjective {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    ∀ (U : X'.Opens) (s : Γ((I.comap f).module, U)), ∀ x ∈ U,
      ∃ (V : X'.Opens) (i : V ≤ U), x ∈ V ∧
        ((I.comap f).module).presheaf.map (homOfLE i).op s ∈
          Set.range ((I.pullbackModuleComparison f).app V) := by
  intro U s x hx
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hfx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (U ⊓ f ⁻¹ᵁ U₀ : X'.Opens) from ⟨hx, hfx⟩) (U ⊓ f ⁻¹ᵁ U₀).isOpen
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  have hVU₀ : V ≤ f ⁻¹ᵁ U₀ := fun y hy => (hVle hy).2
  refine ⟨V, hVU, hxV, ?_⟩
  let M : X.Modules := I.module
  let N : X'.Modules := (I.comap f).module
  let P : X'.Modules := (Scheme.Modules.pullback f).obj M
  let α : P ⟶ N := I.pullbackModuleComparison f
  let η : M ⟶ (Scheme.Modules.pushforward f).obj P :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).unit.app
      (I.module : SheafOfModules X.ringCatSheaf)
  let β : M ⟶ (Scheme.Modules.pushforward f).obj N := I.moduleToPushforwardComapModule f
  let ι : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) := I.moduleι
  let ι' : N ⟶ (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) := (I.comap f).moduleι
  obtain ⟨hrangeV, hinjV⟩ := (I.comap f).range_moduleIota_app_and_injective ⟨V, hV⟩
  obtain ⟨hrangeU₀, -⟩ := I.range_moduleIota_app_and_injective ⟨U₀, hU₀⟩
  let g : Γ(X, U₀) →+* Γ(X', V) := (f.appLE U₀ V hVU₀).hom
  let T : Ideal Γ(X', V) :=
    { carrier := {z | ∃ t : Γ(P, V), ι'.app V (α.app V t) = z}
      add_mem' := by
        rintro _ _ ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
        exact ⟨t₁ + t₂, by rw [map_add, map_add]; rfl⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero]; rfl⟩
      smul_mem' := by
        rintro c _ ⟨t, rfl⟩
        exact ⟨c • t, by erw [Modules.Hom.app_smul, Modules.Hom.app_smul]; rfl⟩ }
  have hα_nat : ∀ y : Γ(P, f ⁻¹ᵁ U₀),
      α.app V (P.presheaf.map (homOfLE hVU₀).op y) =
        N.presheaf.map (homOfLE hVU₀).op (α.app (f ⁻¹ᵁ U₀) y) := fun y =>
    ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE hVU₀).op) y
  have hι'_nat : ∀ y : Γ(N, f ⁻¹ᵁ U₀),
      ι'.app V (N.presheaf.map (homOfLE hVU₀).op y) =
        X'.presheaf.map (homOfLE hVU₀).op (ι'.app (f ⁻¹ᵁ U₀) y) := fun y =>
    ConcreteCategory.congr_hom (ι'.mapPresheaf.naturality (homOfLE hVU₀).op) y
  have hηα : ∀ m : Γ(M, U₀), α.app (f ⁻¹ᵁ U₀) (η.app U₀ m) = β.app U₀ m := fun m => by
    have := I.unit_comp_map_pullbackModuleComparison f
    exact congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj N => φ.app U₀ m) this
  have hβι : ∀ m : Γ(M, U₀), ι'.app (f ⁻¹ᵁ U₀) (β.app U₀ m) = f.app U₀ (ι.app U₀ m) := fun m => by
    have := I.moduleToPushforwardComapModule_comp_map_moduleι f
    exact congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) => φ.app U₀ m) this
  have hT : (I.ideal ⟨U₀, hU₀⟩).map g ≤ T := by
    rw [Ideal.map_le_iff_le_comap]
    intro x₀ hx₀
    obtain ⟨m, hm⟩ : x₀ ∈ Set.range (I.moduleι.app U₀) := by rw [hrangeU₀]; exact hx₀
    refine ⟨P.presheaf.map (homOfLE hVU₀).op (η.app U₀ m), ?_⟩
    erw [hα_nat, hι'_nat, hηα, hβι, ← hm]
    rfl
  have hmem : ι'.app V (N.presheaf.map (homOfLE hVU).op s) ∈ (I.ideal ⟨U₀, hU₀⟩).map g := by
    rw [← lbE_ideal_comap_of_le I f ⟨U₀, hU₀⟩ ⟨V, hV⟩ hVU₀]
    have : ι'.app V (N.presheaf.map (homOfLE hVU).op s) ∈ Set.range ((I.comap f).moduleι.app V) :=
      ⟨_, rfl⟩
    rw [hrangeV] at this
    exact this
  obtain ⟨t, ht⟩ := hT hmem
  exact ⟨t, hinjV ht⟩

end AlgebraicGeometry.Scheme.IdealSheafData

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.pullbackModuleComparison_locallySurjective {X
  X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData) :
    ∀ (U : X'.Opens) (s : Γ((I.comap f).module, U)), ∀ x ∈ U,
      ∃ (V : X'.Opens) (i : V ≤ U), x ∈ V ∧
        ((I.comap f).module).presheaf.map (homOfLE i).op s ∈
          Set.range ((I.pullbackModuleComparison f).app V) :=
  AlgebraicGeometry.Scheme.IdealSheafData.lbE_pullbackModuleComparison_locallySurjective f I
end Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
