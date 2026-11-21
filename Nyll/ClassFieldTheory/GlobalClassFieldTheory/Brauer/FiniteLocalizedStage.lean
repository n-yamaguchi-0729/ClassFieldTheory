/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteStageSupport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralCocycle
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-!
# Finite support of finite-place Brauer localization

The canonical restriction of an inflated cocycle factors through the actual
chosen localization of the finite splitting field. At a good place, that
extension is unramified and the transported coefficients are integer units.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsDedekindDomain NumberField
open LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField NNReal ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K] [NumberField K]

private theorem valuationMap_chosenCompletion_image_eq_zero
    {E : Type u} [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (a : Eˣ)
    (ha : (finitePlaceExtensionCentre v (chosenFinitePlaceExtension (L := E) v)).valuation E
      (a : E) = 1) :
    valuationMap (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v)
      (Additive.ofMul (Units.map (AbsoluteValue.toAlgebraicLocalization
        (HeightOneSpectrum.adicAbv K v) (chosenFinitePlaceExtension (L := E) v).1
        (chosenFinitePlaceExtension (L := E) v).2).toMonoidHom a)) = 0 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := E) v
  let W := finitePlaceExtensionCentre v w
  let M := ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v
  let x : M := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (a : E)
  have hstd : HeightOneSpectrum.adicAbv E W (a : E) = 1 := by
    rw [HeightOneSpectrum.adicAbv_def]
    exact_mod_cast (WithZeroMulInt.toNNReal_eq_one_iff (W.valuation E (a : E))
      (HeightOneSpectrum.absNorm_ne_zero W) (HeightOneSpectrum.one_lt_absNorm_nnreal W).ne').mpr ha
  have hstdInv : HeightOneSpectrum.adicAbv E W ((a : E)⁻¹) = 1 := by
    rw [map_inv₀, hstd, inv_one]
  have hequiv := AbsoluteValue.isEquiv_iff_lt_one_iff.mp (finitePlaceExtension_isEquiv_adicAbv v w)
  have hge : 1 ≤ w.1 (a : E) := by
    apply le_of_not_gt
    intro h
    have hh := (hequiv (a : E)).mp h
    rw [hstd] at hh
    exact lt_irrefl _ hh
  have hgeInv : 1 ≤ w.1 ((a : E)⁻¹) := by
    apply le_of_not_gt
    intro h
    have hh := (hequiv ((a : E)⁻¹)).mp h
    rw [hstdInv] at hh
    exact lt_irrefl _ hh
  rw [map_inv₀] at hgeInv
  have hw := le_antisymm ((one_le_inv₀ (w.1.pos a.ne_zero)).mp hgeInv) hge
  have hnorm : ‖x‖ = 1 :=
    (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2
      (a : E)).trans hw
  let ν : Valuation M ℝ≥0 := Valued.v
  have hν : ν x = ν 1 := by
    change ‖x‖₊ = ‖(1 : M)‖₊
    apply NNReal.eq
    simpa only [coe_nnNorm, norm_one] using hnorm
  apply valuationMap_eq_zero_of_valuation_eq_one
  change ValuativeRel.valuation M x = 1
  rw [← map_one (ValuativeRel.valuation M)]
  apply le_antisymm
  · rw [← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation M),
      Valuation.Compatible.vle_iff_le (v := ν)]
    exact hν.le
  · rw [← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation M),
      Valuation.Compatible.vle_iff_le (v := ν)]
    exact hν.ge

section CompletedStage

variable (v : HeightOneSpectrum (𝓞 K))
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]

local notation "absᵥ" => HeightOneSpectrum.adicAbv K v
local notation "extᵥ" => chosenFinitePlaceExtension (L := E) v
local notation "Kᵥ" => ChosenFinitePlaceBaseCompletion (K := K) v
local notation "E𝑤" => ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v

local instance : Algebra K E𝑤 := localizedCompletionGlobalAlgebra absᵥ extᵥ

local instance : IsScalarTower K Kᵥ E𝑤 := localizedCompletionIsScalarTower absᵥ extᵥ

/-- The original extension embeds in its chosen finite-place completed factor. -/
abbrev chosenCompletedFiniteEmbedding : E →ₐ[K] E𝑤 :=
  localizedCompletionToAlgHom absᵥ extᵥ

/-- The relative restriction to the actual chosen completed extension. -/
def chosenFinitePlaceRelativeRestriction : relativeBr E →+
    continuousCohomology 2 (galoisUnitsRep Kᵥ E𝑤) :=
  embeddedRelativeRestriction (A := Kᵥ) E (chosenCompletedFiniteEmbedding v E)

omit [NumberField E] in
/-- The canonical localization of an inflated class vanishes exactly when
its restriction to the actual chosen completed extension vanishes. -/
theorem finitePlaceRestriction_finiteInflation_eq_zero_iff (x : relativeBr E) :
    finitePlaceRestriction K v (finiteInflation E x) = 0 ↔
      chosenFinitePlaceRelativeRestriction v E x = 0 := by
  let : FiniteDimensional Kᵥ E𝑤 := chosenFinitePlaceLocalizedFiniteDimensional v
  let : IsGalois Kᵥ E𝑤 := chosenFinitePlaceLocalizedIsGalois v
  let e : Kᵥ ≃ₐ[K] v.adicCompletion K := finitePlaceCompletionAlgEquiv v
  let j : E →ₐ[K] E𝑤 := chosenCompletedFiniteEmbedding v E
  let R : relativeBr E →+ continuousCohomology 2 (galoisUnitsRep Kᵥ E𝑤) :=
    embeddedRelativeRestriction (A := Kᵥ) E j
  let S : Br K →+ Br (v.adicCompletion K) := restrict (algebraMap K (v.adicCompletion K))
  have hR : R = chosenFinitePlaceRelativeRestriction v E := rfl
  have hS : S = finitePlaceRestriction K v := rfl
  have h : S (finiteInflation E x) = 0 ↔ R x = 0 :=
    restrict_finiteInflation_eq_zero_iff_embeddedRelativeRestriction
      (A := Kᵥ) (B := v.adicCompletion K) (M := E𝑤) E e j x
  rwa [hS, hR] at h

omit [NumberField E] in
private theorem chosenFinitePlaceIntegralUnitCocycle_class_eq_zero
    (z : ContinuousCohomology.cocycles (galoisUnitsRep Kᵥ E𝑤) 2)
    (hu : ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (hz : ∀ a b c : Gal(E𝑤/Kᵥ),
      valuationMap E𝑤
        (((TopRep.homogeneousCochains (galoisUnitsRep Kᵥ E𝑤)).iCycles 2 z).val a b c) = 0) :
    ContinuousCohomology.π (galoisUnitsRep Kᵥ E𝑤) 2 z = 0 := by
  let : IsNonarchimedeanLocalField Kᵥ := chosenFinitePlaceBaseIsNonarchimedeanLocalField v
  let : IsNonarchimedeanLocalField E𝑤 := chosenFinitePlaceLocalizedIsNonarchimedeanLocalField v
  let : FiniteDimensional Kᵥ E𝑤 := chosenFinitePlaceLocalizedFiniteDimensional v
  let : IsGalois Kᵥ E𝑤 := chosenFinitePlaceLocalizedIsGalois v
  let : IsIntegralClosure 𝒪[E𝑤] 𝒪[Kᵥ] E𝑤 := chosenFinitePlaceLocalizedIsIntegralClosure v
  let : Module.Finite 𝒪[Kᵥ] 𝒪[E𝑤] := chosenFinitePlaceLocalizedIntegerModuleFinite v
  let : IsUnramifiedValuedExtension Kᵥ E𝑤 := hu
  exact unramifiedCocycle_class_eq_zero_of_units Kᵥ E𝑤 z hz

private theorem chosenFinitePlaceRelativeRestriction_eq_zero_of_units
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2)
    (hu : ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (hval : ∀ a, (finitePlaceExtensionCentre v extᵥ).valuation E (relativeCocycleValue E z a : E) =
      1) :
    chosenFinitePlaceRelativeRestriction v E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z) =
      0 := by
  let j : E →ₐ[K] E𝑤 := chosenCompletedFiniteEmbedding v E
  let r : Gal(E𝑤/Kᵥ) →ₜ* Gal(E/K) := embeddedGaloisRestriction (B := Kᵥ) j
  let hr := embeddedGaloisRestriction_commutes (B := Kᵥ) j
  let φ := galoisUnitsMap r j.toRingHom hr
  let zM : ContinuousCohomology.cocycles (galoisUnitsRep Kᵥ E𝑤) 2 :=
    ContinuousCohomology.cocyclesMap r φ 2 z
  let x := ContinuousCohomology.π (galoisUnitsRep K E) 2 z
  have hR : chosenFinitePlaceRelativeRestriction v E = transportCohomology 2 r j.toRingHom hr := rfl
  have hπ : transportCohomology 2 r j.toRingHom hr x =
      ContinuousCohomology.π (galoisUnitsRep Kᵥ E𝑤) 2 zM :=
    ConcreteCategory.congr_hom (ContinuousCohomology.π_map r φ 2) z
  have hvalM (a b c : Gal(E𝑤/Kᵥ)) : valuationMap E𝑤
      (((TopRep.homogeneousCochains (galoisUnitsRep Kᵥ E𝑤)).iCycles 2 zM).val a b c) = 0 := by
    let u := relativeCocycleValue E z (r a, r b, r c)
    have hm : ((TopRep.homogeneousCochains (galoisUnitsRep Kᵥ E𝑤)).iCycles 2 zM).val a b c =
        φ (Additive.ofMul u) := ContinuousCohomology.mappedRelativeCocycle_apply r φ z a b c
    have hφ : (show Additive E𝑤ˣ from φ (Additive.ofMul u)) =
        Additive.ofMul (Units.map j.toMonoidHom u) :=
      galoisUnitsMap_apply r j.toRingHom hr (Additive.ofMul u)
    have hzero : valuationMap E𝑤 (Additive.ofMul (Units.map j.toMonoidHom u)) = 0 :=
      valuationMap_chosenCompletion_image_eq_zero v u (hval (r a, r b, r c))
    exact (congrArg (valuationMap E𝑤) (hm.trans hφ)).trans hzero
  exact (DFunLike.congr_fun hR x).trans
    (hπ.trans (chosenFinitePlaceIntegralUnitCocycle_class_eq_zero v E zM hu hvalM))

/-- A global finite-stage cocycle restricts to zero at the original adic
completion when the chosen completed stage is unramified with unit coefficients. -/
theorem finitePlaceRestriction_finiteInflation_eq_zero
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2)
    (hu : ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (hval : ∀ a, (finitePlaceExtensionCentre v extᵥ).valuation E (relativeCocycleValue E z a : E) =
      1) :
    finitePlaceRestriction K v
      (finiteInflation E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z)) = 0 :=
  (finitePlaceRestriction_finiteInflation_eq_zero_iff v E _).mpr
    (chosenFinitePlaceRelativeRestriction_eq_zero_of_units v E z hu hval)

end CompletedStage

/-- The actual restrictions of a global Brauer class have finite support at finite places. -/
theorem finitePlaceRestriction_hasFiniteSupport (x : Br K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finitePlaceRestriction K v x = 0 := by
  obtain ⟨E, z, he, hsupport⟩ := exists_finiteInflation_unit_support x
  let : NumberField E := NumberField.of_module_finite K E
  obtain ⟨S, hS⟩ := hsupport
  refine ⟨S, fun v hv => ?_⟩
  let w := chosenFinitePlaceExtension (L := E) v
  let W := finitePlaceExtensionCentre v w
  have hW : finitePlaceBelow (K := K) W ∉ S := by
    rw [finitePlaceBelow_finitePlaceExtensionCentre]
    exact hv
  obtain ⟨hu, hval⟩ := hS W hW
  rw [← he]
  exact finitePlaceRestriction_finiteInflation_eq_zero v E z
    (chosenFinitePlaceIsUnramified_of_isUnramifiedAt v hu) hval

end ClassFieldTheory.Brauer
