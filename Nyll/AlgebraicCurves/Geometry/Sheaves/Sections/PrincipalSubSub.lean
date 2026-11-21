/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.lean
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
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleDivisorRangeEqLSpaceOn
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.EqMulEqAddOrdPresentations
public import Nyll.SchemeTheory.Modules.Frames.FrameFromTrivialization
public import Nyll.SchemeTheory.Modules.Tensor.TensorFrames
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Models.FunctionFields.RangeAlgebraMapFunctionFieldEqIInf
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# The principal divisor comparing tensor presentations

For function-field presentations of two invertible modules and their tensor
product, the tensor-product divisor differs from the sum of the original divisors
by a principal divisor.
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
namespace Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
open
  _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
open
  _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

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
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace RatSec
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section TensorCalib

open _root_.CategoryTheory.MonoidalCategory

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
theorem IsFrameOn.ne_zero_of_nontrivial {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M,
    U)}
    (hs : IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

variable {L L' : X.Modules}

theorem exists_forall_tensorSections_eq_mul
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V (L'.presheaf.map (homOfLE h).op m) = φ' U m)
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U)) :
    ∃ f : X.functionField, f ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (t : Γ(L', U)),
      φ'' U (tensorSections s t) = f * φ U s * φ' U t := by
  classical
  obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL.exists_isFrameOn (genericPoint X)
  obtain ⟨U₂, t₂, hη₂, ht₂⟩ := hL'.exists_isFrameOn (genericPoint X)
  let V : X.Opens := U₁ ⊓ U₂
  have : Nonempty V := ⟨⟨genericPoint X, hη₁, hη₂⟩⟩
  let s₀ : Γ(L, V) := rM L inf_le_left s₁
  let t₀ : Γ(L', V) := rM L' inf_le_right t₂
  have hs₀ : IsFrameOn s₀ V := (hs₁.map (homOfLE (inf_le_left : V ≤ U₁))).mono inf_le_left
  have ht₀ : IsFrameOn t₀ V := (ht₂.map (homOfLE (inf_le_right : V ≤ U₂))).mono inf_le_right
  have hst₀ : IsFrameOn (tensorSections s₀ t₀) V := hs₀.tensorSections ht₀
  have hφs : φ V s₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hs₀ (hinj V inferInstance (by rw [h, map_zero]))
  have hφt : φ' V t₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial ht₀ (hinj' V inferInstance (by rw [h, map_zero]))
  have hφst : φ'' V (tensorSections s₀ t₀) ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hst₀ (hinj'' V inferInstance (by rw [h, map_zero]))
  refine ⟨φ'' V (tensorSections s₀ t₀) / (φ V s₀ * φ' V t₀), div_ne_zero hφst (mul_ne_zero hφs hφt),
      ?_⟩
  intro U hU s t
  let W : X.Opens := U ⊓ V
  have : Nonempty W := nonempty_inf U V
  obtain ⟨a, ha⟩ := (hs₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L (inf_le_left : W ≤ U) s)
  obtain ⟨b, hb⟩ := (ht₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L' (inf_le_left : W ≤ U) t)
  simp only at ha hb
  have e1 : φ'' U (tensorSections s t) = algebraMap Γ(X, W) X.functionField (a * b) * φ'' V
      (tensorSections s₀ t₀) := by
    rw [← hnat'' U W inf_le_left inferInstance (tensorSections s t), map_homOfLE_tensorSections]
    change φ'' W (tensorSections (rM L (inf_le_left : W ≤ U) s) (rM L' (inf_le_left : W ≤ U) t)) = _
    rw [← ha, ← hb, tensorSections_smul_left, tensorSections_smul_right, ← mul_smul,
      ← map_homOfLE_tensorSections, hsmul'', hnat'' V W inf_le_right inferInstance]
  have e2 : φ U s = algebraMap Γ(X, W) X.functionField a * φ V s₀ := by
    rw [← hnat U W inf_le_left inferInstance s]
    change φ W (rM L (inf_le_left : W ≤ U) s) = _
    rw [← ha, hsmul, hnat V W inf_le_right inferInstance]
  have e3 : φ' U t = algebraMap Γ(X, W) X.functionField b * φ' V t₀ := by
    rw [← hnat' U W inf_le_left inferInstance t]
    change φ' W (rM L' (inf_le_left : W ≤ U) t) = _
    rw [← hb, hsmul', hnat' V W inf_le_right inferInstance]
  rw [e1, e2, e3, map_mul]
  field_simp

end TensorCalib

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.Modules in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
with_weak_namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules in
open Modules Modules.RatSec AlgebraicCurve _root_.CategoryTheory.MonoidalCategory WithZero in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
            X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set
            X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set
            X.functionField)) :
    let := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by
  intro sharedOwner1
  classical
  obtain ⟨E, ψ, e1, e2, e3, e4, e5⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn
      x L hL
  obtain ⟨E', ψ', e1', e2', e3', e4', e5'⟩ :=
      Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L' hL'
  obtain ⟨E'', ψ'', e1'', e2'', e3'', e4'', e5''⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x (L ⊗ L') (hL.tensor hL')
  obtain ⟨f, hf0, hf⟩ := exists_forall_tensorSections_eq_mul hL hL' ψ ψ' ψ'' e1 e1' e1'' e2 e2' e2''
      e3 e3' e3''
  have hpt : ∀ v : Place K X.functionField, (E'' - E - E') v = v.ord f⁻¹ := by
    intro v
    obtain ⟨y, hy, hv⟩ := exists_closedPoint_range_stalk_eq x v
    obtain ⟨U₁, s₁, hy₁, hs₁⟩ := hL.exists_isFrameOn y
    obtain ⟨U₂, t₂, hy₂, ht₂⟩ := hL'.exists_isFrameOn y
    let W : X.Opens := U₁ ⊓ U₂
    have hyW : y ∈ W := ⟨hy₁, hy₂⟩
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    let s : Γ(L, W) := rM L inf_le_left s₁
    let t : Γ(L', W) := rM L' inf_le_right t₂
    have hs : IsFrameOn s W := (hs₁.map (homOfLE (inf_le_left : W ≤ U₁))).mono inf_le_left
    have ht : IsFrameOn t W := (ht₂.map (homOfLE (inf_le_right : W ≤ U₂))).mono inf_le_right
    have hst : IsFrameOn (tensorSections s t) W := hs.tensorSections ht
    have gen : ∀ {M : X.Modules} (m : Γ(M, W)), IsFrameOn m W →
        ∀ (W' : X.Opens) (h : W' ≤ W), y ∈ W' → ∀ m' : Γ(M, W'), ∃ a : Γ(X, W'),
          m' = a • M.presheaf.map (homOfLE h).op m := by
      intro M m hm W' h _ m'
      obtain ⟨a, ha⟩ := (hm h h).2 m'
      exact ⟨a, ha.symm⟩
    have k := e5 W s y hyW hy (gen s hs) v hv
    have k' := e5' W t y hyW hy (gen t ht) v hv
    have k'' := e5'' W (tensorSections s t) y hyW hy (gen _ hst) v hv
    rw [hf W s t, Valuation.map_mul, Valuation.map_mul, ← k, ← k'] at k''
    have hfv : v.adicValuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf0
    have hfv' : v.adicValuation f = exp (-(v.ord f)) := by
      simp only [Place.ord, neg_neg, WithZero.exp_log hfv]
    rw [hfv', ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_injective.eq_iff] at k''
    simp only [Finsupp.coe_sub, Pi.sub_apply, Place.ord_inv]
    omega
  have hP0 : Divisor.IsPrincipal (E'' - E - E') := ⟨f⁻¹, inv_ne_zero hf0, hpt⟩
  have hsec : ∀ {M : X.Modules}, Scheme.Modules.IsInvertible M → ∃ (U : X.Opens) (m : Γ(M, U)), m ≠
      0 := by
    intro M hM
    obtain ⟨U, s, hη, hs⟩ := hM.exists_isFrameOn (genericPoint X)
    have : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s, IsFrameOn.ne_zero_of_nontrivial hs⟩
  obtain ⟨-, -, -, -, hP1⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x L D E φ
      ψ
    hnat e1 hsmul e2 hinj e3 hrange e4 (hsec hL)
  obtain ⟨-, -, -, -, hP2⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x L' D'
      E' φ' ψ'
    hnat' e1' hsmul' e2' hinj' e3' hrange' e4' (hsec hL')
  obtain ⟨-, -, -, -, hP3⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x (L ⊗
      L') D'' E''
    φ'' ψ'' hnat'' e1'' hsmul'' e2'' hinj'' e3'' hrange'' e4'' (hsec (hL.tensor hL'))
  have key : D'' - D - D' = (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') := by abel
  rw [key]
  have mem : (D'' - E'') - (D - E) - (D' - E') + (E'' - E - E') ∈ Divisor.principal (K := K) (F :=
      X.functionField) :=
    add_mem (sub_mem (sub_mem hP3 hP1) hP2) hP0
  exact mem
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry
    Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.AlgebraicGeometry
    _root_.CategoryTheory.MonoidalCategory in
with_weak_namespace Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
theorem _root_.AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
            X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set
            X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set
            X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') :=
  AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor' x L L' hL hL' D D'
      D'' φ hnat hsmul hinj
    hrange φ' hnat' hsmul' hinj' hrange' φ'' hnat'' hsmul'' hinj'' hrange''
end Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
attribute [-simp]
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
