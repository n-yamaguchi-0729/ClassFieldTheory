/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Nyll.SchemeTheory.Modules.Invertible.Rigidify

/-!
# The native module of an ideal sheaf

The ideal module is the actual kernel of the quotient structure-sheaf map.
These general scheme constructions are shared with the Cartier-divisor consumers.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The canonical map from the structure module to the pushforward structure module. -/
abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The structure-module map to an empty source is zero. -/
theorem Scheme.Hom.unitToPushforwardUnit_eq_zero_of_isEmpty (f : X ⟶ Y) [IsEmpty X] :
    f.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  have h : f ⁻¹ᵁ U.unop = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  have : Subsingleton Γ(X, f ⁻¹ᵁ U.unop) := h ▸ inferInstanceAs (Subsingleton Γ(X, ⊥))
  exact Subsingleton.elim (α := Γ(X, f ⁻¹ᵁ U.unop)) _ _

namespace Scheme.IdealSheafData

/-- The ideal module, realized as the kernel of the quotient structure-sheaf map. -/
def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)

/-- The inclusion of the ideal module into the structure module. -/
def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit

/-- The dual of the ideal module. -/
def invModule (I : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.dual I.module

/-- The module of the unit ideal is canonically the structure module. -/
def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit_eq_zero_of_isEmpty ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The dual of the unit ideal module is canonically the structure module. -/
def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules :=
  Scheme.Modules.dualMapIso topModuleIso ≪≫ MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
