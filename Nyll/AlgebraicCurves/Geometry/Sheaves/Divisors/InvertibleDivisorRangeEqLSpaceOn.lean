/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameGeneration
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Points.Places
public import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.AlgebraicCurves.Models.FunctionFields.RangeAlgebraMapFunctionFieldEqIInf
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Divisor presentations of invertible modules

An invertible module on a smooth integral curve has a compatible presentation in
the function field whose affine images are Riemann-Roch spaces. Local generators
recover the valuation of the representing divisor.
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
namespace Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
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

section Phi

variable [IsIntegral X] (V₀ : X.Opens) [Nonempty V₀]
  (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf)

/-- The function field coordinate of a section, using the fixed nonempty trivialising open. -/
noncomputable def φ (W : X.Opens) [Nonempty W] (m : Γ(M, W)) : X.functionField :=
  haveI := nonempty_inf W V₀
  alg (W ⊓ V₀) (ψ M V₀ e₀ inf_le_right (rM M inf_le_left m))

theorem φ_def (W : X.Opens) [Nonempty W] (m : Γ(M, W)) :
    φ M V₀ e₀ W m = (haveI := nonempty_inf W V₀; alg (W ⊓ V₀) (ψ M V₀ e₀ inf_le_right (rM M
        inf_le_left m))) := rfl

theorem φ_add (W : X.Opens) [Nonempty W] (m m' : Γ(M, W)) :
    φ M V₀ e₀ W (m + m') = φ M V₀ e₀ W m + φ M V₀ e₀ W m' := by
  simp only [φ_def]
  rw [rM_add, ψ_add, alg_add]

theorem φ_zero (W : X.Opens) [Nonempty W] : φ M V₀ e₀ W 0 = 0 := by
  simp only [φ_def]
  rw [rM_zero, ψ_zero, alg_zero]

theorem φ_sub (W : X.Opens) [Nonempty W] (m m' : Γ(M, W)) :
    φ M V₀ e₀ W (m - m') = φ M V₀ e₀ W m - φ M V₀ e₀ W m' := by
  rw [eq_sub_iff_add_eq, ← φ_add, sub_add_cancel]

theorem φ_smul (W : X.Opens) [Nonempty W] (a : Γ(X, W)) (m : Γ(M, W)) :
    φ M V₀ e₀ W (a • m) = alg W a * φ M V₀ e₀ W m := by
  have := nonempty_inf W V₀
  simp only [φ_def]
  rw [rM_smul, ψ_smul, alg_mul, alg_rO]

theorem φ_rM {W W' : X.Opens} [Nonempty W] [Nonempty W'] (h : W' ≤ W) (m : Γ(M, W)) :
    φ M V₀ e₀ W' (rM M h m) = φ M V₀ e₀ W m := by
  have := nonempty_inf W V₀
  have := nonempty_inf W' V₀
  simp only [φ_def]
  have h' : W' ⊓ V₀ ≤ W ⊓ V₀ := inf_le_inf_right V₀ h
  have e1 : rM M (inf_le_left : W' ⊓ V₀ ≤ W') (rM M h m) = rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W)
      m) := by
    rw [rM_rM, rM_rM]
  rw [e1]
  have e2 := ψ_res M V₀ e₀ (inf_le_right : W ⊓ V₀ ≤ V₀) h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m)
  rw [show ψ M V₀ e₀ (inf_le_right : W' ⊓ V₀ ≤ V₀) (rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m))
      = ψ M V₀ e₀ (h'.trans inf_le_right) (rM M h' (rM M (inf_le_left : W ⊓ V₀ ≤ W) m)) from rfl,
          e2, alg_rO]

theorem φ_frame_self : φ M V₀ e₀ V₀ (frame M V₀ e₀) = 1 := by
  have := nonempty_inf V₀ V₀
  simp only [φ_def]
  rw [show ψ M V₀ e₀ (inf_le_right : V₀ ⊓ V₀ ≤ V₀) (rM M (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (frame M V₀
      e₀))
      = ψ M V₀ e₀ (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (rM M (inf_le_left : V₀ ⊓ V₀ ≤ V₀) (frame M V₀ e₀))
          from rfl,
    ψ_rM_frame, alg_one]

theorem φ_injective
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V)
    (W : X.Opens) [Nonempty W] : Function.Injective (φ M V₀ e₀ W) := by
  intro m m' hmm
  rw [← sub_eq_zero] at hmm ⊢
  rw [← φ_sub] at hmm
  set n := m - m' with hn
  clear_value n
  clear hn m m'
  have := nonempty_inf W V₀
  have ha : rM M (inf_le_left : W ⊓ V₀ ≤ W) n = 0 := by
    apply ψ_injective M V₀ e₀ inf_le_right
    rw [ψ_zero]
    exact alg_injective (W ⊓ V₀) (by rw [alg_zero]; exact hmm)
  choose Vx ex hxV using htriv
  have hb : ∀ x : W, rM M (inf_le_left : W ⊓ Vx x ≤ W) n = 0 := by
    intro x
    have : Nonempty (W ⊓ Vx x : X.Opens) := ⟨⟨x, x.2, hxV x⟩⟩
    have := nonempty_inf (W ⊓ Vx x) V₀
    apply ψ_injective M (Vx x) (ex x) inf_le_right
    rw [ψ_zero]
    apply rO_injective (inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ Vx x)
    rw [rO_zero, ← ψ_res, rM_rM]
    have e1 : rM M ((inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ Vx x).trans (inf_le_left : W ⊓ Vx x ≤ W)) n
        = rM M (inf_le_inf_right V₀ inf_le_left : (W ⊓ Vx x) ⊓ V₀ ≤ W ⊓ V₀) (rM M (inf_le_left : W ⊓
            V₀ ≤ W) n) := by
      rw [rM_rM]
    rw [e1, ha, rM_zero, ψ_zero]
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : W => W ⊓ Vx x) W (fun x => homOfLE inf_le_left)
      ?_ n 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, hxV y⟩
  · intro x
    have := hb x
    simp only [rM] at this
    rw [map_zero]
    exact this

theorem φ_frame_ne_zero
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V)
    (V : X.Opens) [Nonempty V] (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    φ M V₀ e₀ V (frame M V e) ≠ 0 := by
  intro h
  have h0 : frame M V e = 0 := φ_injective M V₀ e₀ htriv V (h.trans (φ_zero M V₀ e₀ V).symm)
  have h1 := ψ_frame M V e
  rw [h0, ψ_zero] at h1
  exact zero_ne_one h1

end Phi

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

variable (V₀ : X.Opens) [Nonempty V₀] (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit
    V₀.toScheme.ringCatSheaf)


theorem adicValuation_φ_le_of_isGeneratorAt (U U' : X.Opens) (s : Γ(M, U)) (s' : Γ(M, U')) (y : X)
    (hyU : y ∈ U) (hyU' : y ∈ U') (hy : IsClosed ({y} : Set X)) (hs' : IsGeneratorAt M U' s' y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    let := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    haveI : Nonempty U' := ⟨⟨y, hyU'⟩⟩
    v.adicValuation (φ M V₀ e₀ U s) ≤ v.adicValuation (φ M V₀ e₀ U' s') := by
  intro sharedOwner1
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have : Nonempty U' := ⟨⟨y, hyU'⟩⟩
  have : Nonempty (U ⊓ U' : X.Opens) := ⟨⟨y, hyU, hyU'⟩⟩
  obtain ⟨a, ha⟩ := hs' (U ⊓ U') inf_le_right ⟨hyU, hyU'⟩ (rM M inf_le_left s)
  rw [← φ_rM M V₀ e₀ (inf_le_left : U ⊓ U' ≤ U) s, ha, φ_smul, φ_rM, Valuation.map_mul]
  calc v.adicValuation (alg (U ⊓ U') a) * v.adicValuation (φ M V₀ e₀ U' s')
      ≤ 1 * v.adicValuation (φ M V₀ e₀ U' s') :=
        mul_le_mul_left (adicValuation_alg_le_one x (U ⊓ U') y ⟨hyU, hyU'⟩ hy v hv a) _
    _ = v.adicValuation (φ M V₀ e₀ U' s') := one_mul _

theorem adicValuation_φ_eq_of_isGeneratorAt (U U' : X.Opens) (s : Γ(M, U)) (s' : Γ(M, U')) (y : X)
    (hyU : y ∈ U) (hyU' : y ∈ U') (hy : IsClosed ({y} : Set X))
    (hs : IsGeneratorAt M U s y) (hs' : IsGeneratorAt M U' s' y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    haveI : Nonempty U' := ⟨⟨y, hyU'⟩⟩
    v.adicValuation (φ M V₀ e₀ U s) = v.adicValuation (φ M V₀ e₀ U' s') :=
  le_antisymm (adicValuation_φ_le_of_isGeneratorAt M x V₀ e₀ U U' s s' y hyU hyU' hy hs' v hv)
    (adicValuation_φ_le_of_isGeneratorAt M x V₀ e₀ U' U s' s y hyU' hyU hy hs v hv)

/-- A trivialising open subset together with its module isomorphism to the unit module. -/
structure Triv where
  /-- The open subset on which the module is trivialised. -/
  V : X.Opens
  /-- The chosen isomorphism to the unit module on the trivialising open. -/
  e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf

open Classical in
/-- The valuation exponent of a local generator at the place, and zero outside the represented
    places. -/
noncomputable def dAt (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField) : ℤ
    :=
  letI := (baseToFunctionField x).toAlgebra
  if h : ∃ (y : X) (T : Triv M), y ∈ T.V ∧ IsClosed ({y} : Set X) ∧
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring then
    haveI : Nonempty h.choose_spec.choose.V := ⟨⟨h.choose, h.choose_spec.choose_spec.1⟩⟩
    WithZero.log (v.adicValuation (φ M V₀ e₀ h.choose_spec.choose.V (frame M h.choose_spec.choose.V
        h.choose_spec.choose.e)))
  else 0

theorem exp_dAt_eq [IsSeparated x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V)
    (U : X.Opens) (s : Γ(M, U)) (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (hs : IsGeneratorAt M U s y)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    let := (baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    exp (dAt M x V₀ e₀ v) = v.adicValuation (φ M V₀ e₀ U s) := by
  intro sharedOwner1
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  obtain ⟨V, e, hyV⟩ := htriv y
  have h : ∃ (y : X) (T : Triv M), y ∈ T.V ∧ IsClosed ({y} : Set X) ∧
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring :=
    ⟨y, ⟨V, e⟩, hyV, hy, hv⟩
  rw [dAt, dite_eq_left h]
  obtain ⟨hy'T, hy', hv'⟩ := h.choose_spec.choose_spec
  have hyy : h.choose = y := eq_of_range_stalk_eq x _ _ (hv'.trans hv.symm)
  set T := h.choose_spec.choose with hT
  have : Nonempty T.V := ⟨⟨h.choose, hy'T⟩⟩
  rw [hyy] at hy'T
  have hne : φ M V₀ e₀ T.V (frame M T.V T.e) ≠ 0 := φ_frame_ne_zero M V₀ e₀ htriv T.V T.e
  rw [exp_log (Place.adicValuation_ne_zero _ hne)]
  exact adicValuation_φ_eq_of_isGeneratorAt M x V₀ e₀ T.V U (frame M T.V T.e) s y hy'T hyU hy
    (isGeneratorAt_frame M T.V T.e y) hs v hv

theorem dAt_eq_zero_of_mem [IsSeparated x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V)
    (y : X) (hyV₀ : y ∈ V₀) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    dAt M x V₀ e₀ v = 0 := by
  let := (baseToFunctionField x).toAlgebra
  have h := exp_dAt_eq M x V₀ e₀ htriv V₀ (frame M V₀ e₀) y hyV₀ hy (isGeneratorAt_frame M V₀ e₀ y)
      v hv
  rw [φ_frame_self, Valuation.map_one, ← exp_zero] at h
  exact exp_injective h

omit [SmoothOfRelativeDimension 1 x] in
theorem dAt_eq_zero_of_not (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      ¬ ∃ y : X, IsClosed ({y} : Set X) ∧
        (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    dAt M x V₀ e₀ v = 0 := by
  let := (baseToFunctionField x).toAlgebra
  rw [dAt, dite_eq_right]
  rintro ⟨y, T, -, hy, hvy⟩
  exact hv ⟨y, hy, hvy⟩

theorem finite_support_dAt [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V) :
    (Function.support (dAt M x V₀ e₀)).Finite := by
  let := (baseToFunctionField x).toAlgebra
  have hV₀ : ((V₀ : Set X)).Nonempty := by
    obtain ⟨⟨z, hz⟩⟩ := (inferInstance : Nonempty V₀)
    exact ⟨z, hz⟩
  have hfin := finite_compl_of_isOpen x V₀ hV₀
  apply (hfin.biUnion (t := fun y => {v : Place K X.functionField |
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring})
          ?_).subset
  · intro v hv
    rw [Function.mem_support] at hv
    by_cases h : ∃ y : X, IsClosed ({y} : Set X) ∧
        (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
    · obtain ⟨y, hy, hvy⟩ := h
      refine Set.mem_biUnion (x := y) ?_ hvy
      intro hyV₀
      exact hv (dAt_eq_zero_of_mem M x V₀ e₀ htriv y hyV₀ hy v hvy)
    · exact (hv (dAt_eq_zero_of_not M x V₀ e₀ v h)).elim
  · intro y _
    apply Set.Subsingleton.finite
    intro v hv w hw
    apply Place.ext
    apply ValuationSubring.toSubring_injective
    exact hv.symm.trans hw

/-- The divisor defined by the valuation exponents of local generators relative to the fixed
    coordinate. -/
noncomputable def divisor [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V) :
    letI := (baseToFunctionField x).toAlgebra
    Divisor K X.functionField :=
  Finsupp.ofSupportFinite (dAt M x V₀ e₀) (finite_support_dAt M x V₀ e₀ htriv)

theorem divisor_apply [IsSeparated x] [QuasiCompact x]
    (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf), x ∈ V)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField) :
    divisor M x V₀ e₀ htriv v = dAt M x V₀ e₀ v := by
  simp only [divisor, Finsupp.ofSupportFinite_coe]

end Places

section Main

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 x]
  [IsSeparated x] [QuasiCompact x]
  (V₀ : X.Opens) [Nonempty V₀] (e₀ : M.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf)
  (htriv : ∀ x : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf), x ∈ V)

theorem φ_mem_lSpaceOn (U : X.Opens) [Nonempty U] (m : Γ(M, U)) :
    let := (baseToFunctionField x).toAlgebra
    φ M V₀ e₀ U m ∈ lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv) := by
  intro sharedOwner1 v hv
  obtain ⟨y, hyU, hy, hvy⟩ := hv
  obtain ⟨V, e, hyV⟩ := htriv y
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨y, hyU, hyV⟩⟩
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  rw [divisor_apply, exp_dAt_eq M x V₀ e₀ htriv V (frame M V e) y hyV hy (isGeneratorAt_frame M V e
      y) v hvy,
    ← φ_rM M V₀ e₀ (inf_le_left : U ⊓ V ≤ U) m,
    eq_smul_frame M V e (inf_le_right : U ⊓ V ≤ V) (rM M (inf_le_left : U ⊓ V ≤ U) m), φ_smul, φ_rM,
    Valuation.map_mul]
  calc v.adicValuation (alg (U ⊓ V) _) * v.adicValuation (φ M V₀ e₀ V (frame M V e))
      ≤ 1 * v.adicValuation (φ M V₀ e₀ V (frame M V e)) :=
        mul_le_mul_left (adicValuation_alg_le_one x (U ⊓ V) y ⟨hyU, hyV⟩ hy v hvy _) _
    _ = v.adicValuation (φ M V₀ e₀ V (frame M V e)) := one_mul _

theorem exists_φ_eq (U : X.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] (f : X.functionField)
    (hf : letI := (baseToFunctionField x).toAlgebra
      f ∈ lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv)) :
    ∃ m : Γ(M, U), φ M V₀ e₀ U m = f := by
  let := (baseToFunctionField x).toAlgebra
  have htriv' := htriv
  choose Vt et hyt using htriv'
  have hW : ∀ y : U, ∃ g : Γ(X, U), X.basicOpen g ≤ U ⊓ Vt y ∧ (y : X) ∈ X.basicOpen g :=
    fun y => hU.exists_basicOpen_le (V := U ⊓ Vt y) ⟨(y : X), ⟨y.2, hyt y⟩⟩ y.2
  choose g hgle hyg using hW
  let W : U → X.Opens := fun y => X.basicOpen (g y)
  have hWU : ∀ y, W y ≤ U := fun y => (hgle y).trans inf_le_left
  have hWV : ∀ y, W y ≤ Vt y := fun y => (hgle y).trans inf_le_right
  have hWaff : ∀ y, IsAffineOpen (W y) := fun y => hU.basicOpen (g y)
  have hWne : ∀ y, Nonempty (W y) := fun y => ⟨⟨y, hyg y⟩⟩
  have hVne : ∀ y, Nonempty (Vt y) := fun y => ⟨⟨y, hyt y⟩⟩
  let c : U → X.functionField := fun y => φ M V₀ e₀ (Vt y) (frame M (Vt y) (et y))
  have hc : ∀ y, c y ≠ 0 := fun y => φ_frame_ne_zero M V₀ e₀ htriv (Vt y) (et y)
  have hreg : ∀ y : U, f * (c y)⁻¹ ∈ (algebraMap Γ(X, W y) X.functionField).range := by
    intro y
    rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x (W y) (hWaff y)]
    refine Subring.mem_iInf.mpr fun v' => Subring.mem_iInf.mpr fun ⟨z, hzW, hz, hv'z⟩ => ?_
    apply (Place.mem_iff_adicValuation_le_one v').mpr
    have h1 : v'.adicValuation f ≤ exp (divisor M x V₀ e₀ htriv v') :=
      hf v' ⟨z, hWU y hzW, hz, hv'z⟩
    rw [divisor_apply, exp_dAt_eq M x V₀ e₀ htriv (Vt y) (frame M (Vt y) (et y)) z (hWV y hzW) hz
      (isGeneratorAt_frame M (Vt y) (et y) z) v' hv'z] at h1
    rw [Valuation.map_mul, map_inv₀]
    have hcv : v'.adicValuation (c y) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc y)
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ (zero_lt_iff.mpr hcv)).mpr h1
  choose a ha using hreg
  let ml : ∀ y : U, Γ(M, W y) := fun y => a y • rM M (hWV y) (frame M (Vt y) (et y))
  have hml : ∀ y, φ M V₀ e₀ (W y) (ml y) = f := by
    intro y
    simp only [ml]
    rw [φ_smul, φ_rM]
    change (algebraMap Γ(X, W y) X.functionField) (a y) * c y = f
    rw [ha, mul_assoc, inv_mul_cancel₀ (hc y), mul_one]
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 W ml := by
    intro i j
    have := nonempty_inf (W i) (W j)
    have key : rM M (inf_le_left : W i ⊓ W j ≤ W i) (ml i) = rM M (inf_le_right : W i ⊓ W j ≤ W j)
        (ml j) := by
      apply φ_injective M V₀ e₀ htriv (W i ⊓ W j)
      rw [φ_rM, φ_rM, hml, hml]
    simp only [rM] at key
    rw [show Opens.infLELeft (W i) (W j) = homOfLE inf_le_left from Subsingleton.elim _ _,
      show Opens.infLERight (W i) (W j) = homOfLE inf_le_right from Subsingleton.elim _ _]
    exact key
  have hcover : U ≤ iSup W := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyg ⟨z, hz⟩⟩
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' F W U (fun y => homOfLE (hWU y)) hcover ml
      hcompat
  refine ⟨m, ?_⟩
  obtain ⟨y₀⟩ := (inferInstance : Nonempty U)
  have hm0 : rM M (hWU y₀) m = ml y₀ := hm y₀
  have : Nonempty (W y₀) := hWne y₀
  exact (φ_rM M V₀ e₀ (hWU y₀) m).symm.trans
    ((congrArg (φ M V₀ e₀ (W y₀)) hm0).trans (hml y₀))

theorem range_φ_eq (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let := (baseToFunctionField x).toAlgebra
    Set.range (φ M V₀ e₀ U) = (lSpaceOn (placesOf x U) (divisor M x V₀ e₀ htriv) : Set
        X.functionField) := by
  intro sharedOwner1
  ext f
  constructor
  · rintro ⟨m, rfl⟩
    exact φ_mem_lSpaceOn M x V₀ e₀ htriv U m
  · intro hf
    exact exists_φ_eq M x V₀ e₀ htriv U hU f hf

end Main

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace IsInvertible
end AlgebraicGeometry.Scheme.Modules.IsInvertible
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
    _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
open AlgebraicGeometry.Scheme.Modules.RatSec AlgebraicCurve in
theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    let := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField
        : Type u)),
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
              X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(M, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • M.presheaf.map
              (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
                →
            WithZero.exp (D v) = v.adicValuation (φ U s)) := by
  intro sharedOwner1
  classical
  have htriv : ∀ z : X, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf), z ∈ V := by
    intro z
    obtain ⟨V, hzV, ⟨e⟩⟩ := hM.1 z
    exact ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ e, hzV⟩
  obtain ⟨V₀, e₀, hηV₀⟩ := htriv (genericPoint X)
  have : Nonempty V₀ := ⟨⟨genericPoint X, hηV₀⟩⟩
  let D := divisor M x V₀ e₀ htriv
  let φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u) := fun U =>
    if hU : Nonempty U then
      { toFun := fun m => φ M V₀ e₀ U m
        map_zero' := φ_zero M V₀ e₀ U
        map_add' := φ_add M V₀ e₀ U }
    else 0
  have hφ' : ∀ (U : X.Opens) [hU : Nonempty U] (m : Γ(M, U)), φ' U m = φ M V₀ e₀ U m := by
    intro U hU m
    simp only [φ', dite_eq_left hU]
    rfl
  refine ⟨D, φ', ?_, ?_, ?_, ?_, ?_⟩
  · intro U V h hV m
    have := hV
    have : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
    rw [hφ', hφ']
    exact φ_rM M V₀ e₀ h m
  · intro U hU a m
    rw [hφ', hφ']
    exact φ_smul M V₀ e₀ U a m
  · intro U hU m m' h
    rw [hφ', hφ'] at h
    exact φ_injective M V₀ e₀ htriv U h
  · intro U hU hne
    have := hne
    have : (φ' U : Γ(M, U) → X.functionField) = φ M V₀ e₀ U := funext fun m => hφ' U m
    rw [this]
    exact range_φ_eq M x V₀ e₀ htriv U hU
  · intro U s y hyU hy hs v hv
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    rw [hφ']
    simp only [D, divisor_apply]
    exact exp_dAt_eq M x V₀ e₀ htriv U s y hyU hy hs v hv

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (D : AlgebraicCurve.Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField
        : Type u)),
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set
              X.functionField)) ∧
      (∀ (U : X.Opens) (s : Γ(M, U)) (y : X), y ∈ U → IsClosed ({y} : Set X) →
          (∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • M.presheaf.map
              (homOfLE h).op s) →
          ∀ v : AlgebraicCurve.Place K X.functionField,
            (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring
                →
            WithZero.exp (D v) = v.adicValuation (φ U s)) :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn' x M hM
end Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
