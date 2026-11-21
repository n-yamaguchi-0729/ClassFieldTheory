/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameGeneration
public import Mathlib.Util.WithWeakNamespace
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Points.Places
public import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleDivisorRangeEqLSpaceOn
public import Nyll.SchemeTheory.Modules.EqMulPresentations
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Models.FunctionFields.RangeAlgebraMapFunctionFieldEqIInf
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Divisors representing invertible ideal modules

The module of an invertible ideal has a function-field presentation by affine
Riemann-Roch spaces. Its inclusion in the unit module fixes a rational multiplier
whose orders relate the presenting divisor to local generators of the ideal.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization (rM rO rM_rM rO_rO rM_self rO_self
  rM_smul hat_eq le_hat hat_le eApp eInv eInv_eApp eApp_eInv eApp_zero eApp_injective
  restrict_smul_eq eApp_smul eApp_res ψ ψinv rM_roundtrip rM_roundtrip' rO_roundtrip rO_roundtrip'
  ψ_ψinv ψinv_ψ ψ_injective ψ_zero ψ_smul ψ_res)

section ProofImplementation

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization
  (frame ψ_frame ψ_rM_frame eq_smul_frame IsGeneratorAt isGeneratorAt_frame isGeneratorAt_rM)

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace RatSec
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules)

theorem rM_add {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y + y') = rM M h y + rM M h y' := map_add _ _ _

theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y - y') = rM M h y - rM M h y' := map_sub _ _ _
omit M in
theorem rO_one {V W : X.Opens} (h : V ≤ W) : rO h (1 : Γ(X, W)) = 1 := map_one _
omit M in
theorem rO_mul {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) : rO h (a * b) = rO h a * rO h b :=
    map_mul _ _ _
omit M in
theorem rO_zero {V W : X.Opens} (h : V ≤ W) : rO h (0 : Γ(X, W)) = 0 := map_zero _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem eApp_add (W : X.Opens) (m m' : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (m + m') = eApp M V e W m + eApp M V e W m' := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_add
        m m'

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ]
  rw [rM_add, eApp_add]
  exact map_add _ _ _


end Transport

section Integral

variable [IsIntegral X]

omit M in
theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W :
    X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩
omit M in
/-- The image of a regular function in the function field. -/
noncomputable abbrev alg (U : X.Opens) [Nonempty U] (a : Γ(X, U)) : X.functionField :=
  (X.germToFunctionField U).hom a
omit M in
theorem alg_rO {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) (a : Γ(X, U)) :
    alg W (rO h a) = alg U a := by
  change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W).hom a = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]
omit M in
theorem alg_injective (U : X.Opens) [Nonempty U] : Function.Injective (alg (X := X) U) :=
  Scheme.germToFunctionField_injective X U
omit M in
theorem rO_injective {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) :
    Function.Injective (rO (X := X) h) := by
  intro a b hab
  apply alg_injective U
  rw [← alg_rO h, ← alg_rO h, hab]
omit M in
theorem alg_one (U : X.Opens) [Nonempty U] : alg U (1 : Γ(X, U)) = 1 := map_one _
omit M in
theorem alg_zero (U : X.Opens) [Nonempty U] : alg U (0 : Γ(X, U)) = 0 := map_zero _
omit M in
theorem alg_add (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a + b) = alg U a + alg U b :=
    map_add _ _ _
omit M in
theorem alg_mul (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a * b) = alg U a * alg U b :=
    map_mul _ _ _

end Integral

section Places

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 x]

omit M in
theorem adicValuation_alg_le_one (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (a : Γ(X, W)) :
    let := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W a) ≤ 1 := by
  intro sharedOwner1
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  obtain ⟨W', hW'aff, hyW', hW'W⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hyW
  have : Nonempty W' := ⟨⟨y, hyW'⟩⟩
  rw [← alg_rO hW'W a]
  apply (Place.mem_iff_adicValuation_le_one v).mp
  have hmem : alg W' (rO hW'W a) ∈ (algebraMap Γ(X, W') X.functionField).range := ⟨rO hW'W a, rfl⟩
  rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x W' hW'aff] at hmem
  have h2 := (Subring.mem_iInf.mp hmem) v
  have h3 := (Subring.mem_iInf.mp h2) ⟨y, hyW', hy, hv⟩
  exact h3


end Places

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
namespace PresMod
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.Modules
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
with_weak_namespace AlgebraicGeometry.Scheme.Modules
open RatSec
open _root_.AlgebraicCurve
open _root_.WithZero

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The regular function corresponding to a section of the ideal module. -/
noncomputable def fn (U : X.Opens) (m : Γ(I.module, U)) : Γ(X, U) :=
  ofUnitSection U (I.moduleι.app U m)

theorem fn_add (U : X.Opens) (m m' : Γ(I.module, U)) : fn I U (m + m') = fn I U m + fn I U m' := by
  simp only [fn, map_add]; rfl

theorem fn_zero (U : X.Opens) : fn I U (0 : Γ(I.module, U)) = 0 := by
  simp only [fn, map_zero]; rfl

theorem fn_sub (U : X.Opens) (m m' : Γ(I.module, U)) : fn I U (m - m') = fn I U m - fn I U m' := by
  simp only [fn, map_sub]; rfl

theorem fn_smul (U : X.Opens) (a : Γ(X, U)) (m : Γ(I.module, U)) : fn I U (a • m) = a * fn I U m :=
    by
  simp only [fn, Scheme.Modules.Hom.app_smul]; rfl

theorem fn_rM {U W : X.Opens} (h : W ≤ U) (m : Γ(I.module, U)) :
    fn I W (rM I.module h m) = rO h (fn I U m) := by
  simp only [fn, rM, rO]
  have nat := (I.moduleι.mapPresheaf).naturality (homOfLE h).op
  have hx := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(I.module, U) → Γ(𝟙_ X.Modules,
      W))) nat) m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  rw [hx]
  rfl

theorem fn_injective_affine (U : X.Opens) (hU : IsAffineOpen U) : Function.Injective (fn I U) := by
  intro m m' h
  exact (range_moduleIota_app_and_injective I ⟨U, hU⟩).2 (ofUnitSection_injective U h)

theorem range_fn_affine (U : X.Opens) (hU : IsAffineOpen U) :
    Set.range (fn I U) = (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
  have h := (range_moduleIota_app_and_injective I ⟨U, hU⟩).1
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    have hm : (I.moduleι.app U m : Γ(𝟙_ X.Modules, U)) ∈ Set.range (I.moduleι.app (⟨U, hU⟩ :
        X.affineOpens)) := ⟨m, rfl⟩
    rw [h] at hm
    exact hm
  · intro hg
    have hg' : (toUnitSection U g) ∈ Set.range (I.moduleι.app (⟨U, hU⟩ : X.affineOpens)) := by
      rw [h]
      exact hg
    obtain ⟨m, hm⟩ := hg'
    refine ⟨m, ?_⟩
    simp only [fn]
    rw [hm]
    rfl

theorem fn_injective (U : X.Opens) : Function.Injective (fn I U) := by
  intro m m' hmm
  rw [← sub_eq_zero] at hmm ⊢
  rw [← fn_sub] at hmm
  set n := m - m' with hn
  clear_value n
  clear hn m m'
  have hloc : ∀ (W : X.Opens) (hW : IsAffineOpen W) (h : W ≤ U), rM I.module h n = 0 := by
    intro W hW h
    apply fn_injective_affine I W hW
    rw [fn_rM, hmm, fn_zero, rO_zero]
  let F : TopCat.Sheaf Ab X := ⟨I.module.presheaf, I.module.isSheaf⟩
  have hcov : ∀ z : U, ∃ W : X.Opens, IsAffineOpen W ∧ (z : X) ∈ W ∧ W ≤ U := by
    intro z
    obtain ⟨W, hWaff, hzW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) z.2
    exact ⟨W, hWaff, hzW, hWU⟩
  choose W hWaff hzW hWU using hcov
  refine TopCat.Sheaf.eq_of_locally_eq' F W U (fun z => homOfLE (hWU z)) ?_ n 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hzW ⟨y, hy⟩⟩
  · intro z
    have := hloc (W z) (hWaff z) (hWU z)
    simp only [rM] at this
    rw [map_zero]
    exact this

section Curve

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 x]

omit x [IsIntegral X] [SmoothOfRelativeDimension 1 x] in
theorem frame_ne_zero (V : X.Opens) [Nonempty V]
    (e : I.module.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) : frame I.module V e ≠
        0 := by
  intro h
  have h1 := ψ_frame I.module V e
  rw [h, ψ_zero] at h1
  exact zero_ne_one h1

theorem adicValuation_alg_eq_of_span_eq (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} :
    Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (g g' : Γ(X, W)) (hgg' : Ideal.span {g} = Ideal.span {g'}) :
    let := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W g) = v.adicValuation (alg W g') := by
  intro sharedOwner1
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have h1 : g ∈ Ideal.span {g'} := hgg' ▸ Ideal.mem_span_singleton_self g
  have h2 : g' ∈ Ideal.span {g} := hgg'.symm ▸ Ideal.mem_span_singleton_self g'
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
  apply le_antisymm
  · rw [← ha, alg_mul, Valuation.map_mul]
    calc v.adicValuation (alg W a) * v.adicValuation (alg W g')
        ≤ 1 * v.adicValuation (alg W g') :=
          mul_le_mul_left (adicValuation_alg_le_one x W y hyW hy v hv a) _
      _ = v.adicValuation (alg W g') := one_mul _
  · rw [← hb, alg_mul, Valuation.map_mul]
    calc v.adicValuation (alg W b) * v.adicValuation (alg W g)
        ≤ 1 * v.adicValuation (alg W g) :=
          mul_le_mul_left (adicValuation_alg_le_one x W y hyW hy v hv b) _
      _ = v.adicValuation (alg W g) := one_mul _

end Curve

end AlgebraicGeometry.Scheme.IdealSheafData.PresMod

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
namespace IsInvertible
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
with_weak_namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules in
open Modules Modules.RatSec IdealSheafData.PresMod AlgebraicCurve in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
theorem
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    let := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.module, U), φ V (I.module.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
              X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.module, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.module, W), ∃ a : Γ(X, W), m = a •
              I.module.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
                →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      ∃ c : X.functionField, c ≠ 0 ∧
        (∀ (U : X.Opens) [Nonempty U] (m : Γ(I.module, U)),
            φ U m = c * algebraMap Γ(X, U) X.functionField (Scheme.Modules.ofUnitSection U
                (I.moduleι.app U m))) ∧
        (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} :
            Set X) →
            I.ideal ⟨U, hU⟩ = Ideal.span {g} →
            ∀ v : AlgebraicCurve.Place K X.functionField,
              (algebraMap (X.presheaf.stalk y) X.functionField).range =
                  v.toValuationSubring.toSubring →
              haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
              D v + v.ord c + v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by
  intro sharedOwner1
  classical
  have hM : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  obtain ⟨D, φ, h1, h2, h3, h4, h5⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x I.module hM
  have htriv : ∀ z : X, ∃ (V : X.Opens) (_ : I.module.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf),
      z ∈ V := by
    intro z
    obtain ⟨V, hzV, ⟨e⟩⟩ := hM.1 z
    exact ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app I.module ≪≫ e, hzV⟩
  let φ₀ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u) := fun U =>
    if hU : Nonempty U then
      { toFun := fun m => alg U (fn I U m)
        map_zero' := by rw [fn_zero, alg_zero]
        map_add' := fun m m' => by rw [fn_add, alg_add] }
    else 0
  have hφ₀ : ∀ (U : X.Opens) [hU : Nonempty U] (m : Γ(I.module, U)), φ₀ U m = alg U (fn I U m) := by
    intro U hU m
    simp only [φ₀, dite_eq_left hU]
    rfl
  have n1 : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(I.module, U), φ₀ V (I.module.presheaf.map (homOfLE h).op m) = φ₀ U m := by
    intro U V h hV m
    have := hV
    have : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
    rw [hφ₀, hφ₀]
    change alg V (fn I V (rM I.module h m)) = _
    rw [fn_rM, alg_rO]
  have n2 : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
      φ₀ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ₀ U m := by
    intro U hU a m
    rw [hφ₀, hφ₀, fn_smul, alg_mul]
    rfl
  have n3 : ∀ U : X.Opens, Nonempty U → Function.Injective (φ₀ U) := by
    intro U hU m m' h
    rw [hφ₀, hφ₀] at h
    exact fn_injective I U (alg_injective U h)
  obtain ⟨V₀, e₀, hηV₀⟩ := htriv (genericPoint X)
  have : Nonempty V₀ := ⟨⟨genericPoint X, hηV₀⟩⟩
  have hsec : ∃ (U : X.Opens) (m : Γ(I.module, U)), m ≠ 0 := ⟨V₀, frame I.module V₀ e₀,
      frame_ne_zero I V₀ e₀⟩
  obtain ⟨c, hc0, hc⟩ := Scheme.Modules.exists_forall_eq_mul_of_presentations I.module φ₀ φ n1 h1 n2
      h2 n3 h3 hsec
  refine ⟨D, φ, ⟨h1, h2, h3, h4, h5⟩, c, hc0, ?_, ?_⟩
  · intro U hU m
    rw [hc U m, hφ₀]
    rfl
  · intro U hU g y hyU hy hg v hv
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    obtain ⟨V, e, hyV⟩ := htriv y
    obtain ⟨W, hWaff, hyW, hWle⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
    have hWU : W ≤ U := hWle.trans inf_le_left
    have hWV : W ≤ V := hWle.trans inf_le_right
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    let s : Γ(I.module, W) := rM I.module hWV (frame I.module V e)
    have hs : IsGeneratorAt I.module W s y := isGeneratorAt_rM I.module hWV _ y (isGeneratorAt_frame
        I.module V e y)
    let g' : Γ(X, W) := fn I W s
    have hIW : I.ideal ⟨W, hWaff⟩ = Ideal.span {rO hWU g} := by
      rw [← I.map_ideal (U := ⟨W, hWaff⟩) (V := ⟨U, hU⟩) hWU, hg, Ideal.map_span,
          Set.image_singleton]
      rfl
    have hspan : Ideal.span {g'} = Ideal.span {rO hWU g} := by
      rw [← hIW]
      apply le_antisymm
      · rw [Ideal.span_singleton_le_iff_mem]
        have : g' ∈ Set.range (fn I W) := ⟨s, rfl⟩
        rw [range_fn_affine I W hWaff] at this
        exact this
      · intro f hf
        have hf' : f ∈ Set.range (fn I W) := by rw [range_fn_affine I W hWaff]; exact hf
        obtain ⟨m, rfl⟩ := hf'
        obtain ⟨a, ha⟩ := hs W le_rfl hyW m
        rw [ha, rM_self, fn_smul]
        exact Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self _)
    have key := h5 W s y hyW hy (fun W' h hyW' m => hs W' h hyW' m) v hv
    rw [hc W s, hφ₀, Valuation.map_mul] at key
    change WithZero.exp (D v) = v.adicValuation c * v.adicValuation (alg W g') at key
    rw [adicValuation_alg_eq_of_span_eq x W y hyW hy v hv g' (rO hWU g) hspan, alg_rO] at key
    have hc' : v.adicValuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hg' : v.adicValuation (alg U g) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at key
      exact WithZero.exp_ne_zero key
    have := congrArg WithZero.log key
    rw [WithZero.log_exp, WithZero.log_mul hc' hg'] at this
    simp only [Place.ord]
    change D v + -WithZero.log (v.adicValuation c) + -WithZero.log (v.adicValuation (alg U g)) = 0
    omega
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry
    Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn.AlgebraicGeometry
    _root_.CategoryTheory.MonoidalCategory in
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
with_weak_namespace AlgebraicGeometry.Scheme.IdealSheafData
open IsInvertible in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
theorem exists_divisor_range_module_eq_lSpaceOn
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(I.module, U) →+ (X.functionField : Type u)),
      ((∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(I.module, U), φ V (I.module.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(I.module, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
              X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(I.module, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(I.module, W), ∃ a : Γ(X, W), m = a •
              I.module.presheaf.map (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
                →
            WithZero.exp (D v) = v.adicValuation (φ U s))) ∧
      ∃ c : X.functionField, c ≠ 0 ∧
        (∀ (U : X.Opens) [Nonempty U] (m : Γ(I.module, U)),
            φ U m = c * algebraMap Γ(X, U) X.functionField (Scheme.Modules.ofUnitSection U
                (I.moduleι.app U m))) ∧
        (∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} :
            Set X) →
            I.ideal ⟨U, hU⟩ = Ideal.span {g} →
            ∀ v : AlgebraicCurve.Place K X.functionField,
              (algebraMap (X.presheaf.stalk y) X.functionField).range =
                  v.toValuationSubring.toSubring →
              haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
              D v + v.ord c + v.ord (algebraMap Γ(X, U) X.functionField g) = 0) :=
  exists_divisor_range_module_eq_lSpaceOn' x hI
end Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
