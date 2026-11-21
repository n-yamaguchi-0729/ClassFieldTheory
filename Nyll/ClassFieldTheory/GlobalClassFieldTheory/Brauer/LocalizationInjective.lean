/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionUniverse
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.DirectSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteFieldUnitsIdelePrimitive
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SupportedIdeleH2Localization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorDiagonalCoordinates
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteIdeleLocalH2

/-! # Injectivity of localization for actual global Brauer classes -/

@[expose] public section

noncomputable section

open CategoryTheory IsDedekindDomain NumberField ContinuousCohomology
open AlgebraicNumberTheory RelativeIdeleGroup.Cohomology
open ClassFieldTower.Martinet.Shafarevich CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped NumberField DirectSum

namespace ClassFieldTheory.Brauer

variable {K : Type} [Field K] [NumberField K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Supported" =>
  relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := E) S
local instance : MulDistribMulAction Gal(E/K) Supported :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := E) S

private theorem principalIdele_mem_supported (a : Eˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E),
      finitePlaceBelow (K := K) w ∉ S → w.valuation E (a : E) = 1) :
    RelativeIdeleGroup.principalIdele K E a ∈ Supported := by
  apply (relativeIdeleBaseChange_mem_supportedAt_iff (K := K) (L := E) S _).mpr
  rw [relativeIdeleBaseChangeMulEquiv_principalIdele]
  apply (principalIdele_mem_supportedAt_iff_sUnit (finitePlacesAbove (K := K) (L := E) S) a).mpr
  intro w hw
  exact ha w (fun h => hw ((mem_finitePlacesAbove_iff S w).mpr h))

variable (z : cocycles (galoisUnitsRep K E) 2)
    (hval : ∀ w : HeightOneSpectrum (𝓞 E), finitePlaceBelow (K := K) w ∉ S →
      ∀ a, w.valuation E (relativeCocycleValue E z a : E) = 1)

private def supportedDiagonalCocycle : groupCohomology.cocycles₂
    (Rep.ofMulDistribMulAction Gal(E/K) Supported) := by
  let A := Rep.ofMulDistribMulAction Gal(E/K) Supported
  let B := (finiteIdeleShortComplex K E).X₂
  let c := dehomogenizeTwoOriginal (galoisUnitsRep K E) z
  let cI := groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(E/K)))
    (finiteFieldUnitsIdeleRepHom K E) c
  let ι := GlobalClassFieldTheory.Cohomology.supportedIdeleInclusionRepHom K E S
  let d (p : Gal(E/K) × Gal(E/K)) : A :=
    Additive.ofMul ⟨RelativeIdeleGroup.principalIdele K E
      (show Additive Eˣ from c p).toMul,
      principalIdele_mem_supported E S _ (fun w hw => hval w hw (1, p.1, p.1 * p.2))⟩
  have hι : Function.Injective ι := Subtype.val_injective
  have hdI : groupCohomology.cochainsMap₂ (MonoidHom.id (Gal(E/K))) ι d = cI := rfl
  refine ⟨d, ?_⟩
  rw [groupCohomology.cocycles₂, LinearMap.mem_ker]
  funext p
  apply hι
  have h := congrFun (ConcreteCategory.congr_hom
    (groupCohomology.mapShortComplexH2 (MonoidHom.id (Gal(E/K))) ι).comm₂₃ d) p
  change ι (((groupCohomology.d₂₃ A).hom d) p) =
    ((groupCohomology.d₂₃ B).hom
      (groupCohomology.cochainsMap₂ (MonoidHom.id (Gal(E/K))) ι d)) p at h
  have hcI : (groupCohomology.d₂₃ B).hom cI = 0 := cI.property
  rw [hdI, hcI] at h
  exact h.trans ι.hom.toLinearMap.map_zero.symm

include hval in
private theorem supportedDiagonal_finite_coordinate_eq_zero
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
    (hf : finitePlaceRestriction K v.val
      (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0) :
    groupCohomology.map (MonoidHom.id (Gal(E/K))) (supportedSPlaceFiniteRepHom K E S v) 2
      (groupCohomology.H2π _ (supportedDiagonalCocycle E S z hval)) = 0 := by
  let c := dehomogenizeTwoOriginal (galoisUnitsRep K E) z
  let d := supportedDiagonalCocycle E S z hval
  let r := MonoidHom.id (Gal(E/K))
  have h := finitePlaceTensorDiagonalH2_eq_zero_of_localization v.val E z hf
  let p := supportedSPlaceFiniteRepHom K E S v
  let q := tensorDiagonalRepHom (K := K) (L := E) (v.val.adicCompletion K)
  have hd : groupCohomology.mapCocycles₂ r p d = groupCohomology.mapCocycles₂ r q c := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    change supportedSPlaceFiniteRepHom K E S v
      (Additive.ofMul
        ⟨RelativeIdeleGroup.principalIdele K E (show Additive Eˣ from c (a, b)).toMul, _⟩) =
      tensorDiagonalRepHom (v.val.adicCompletion K) (c (a, b))
    rw [supportedSPlaceFiniteRepHom_apply]
    exact finitePlaceTensorDiagonal_principal v.val (show Additive Eˣ from c (a, b)).toMul
  have hp := groupCohomology.H2π_comp_map_apply r p d
  have hq := groupCohomology.H2π_comp_map_apply r q c
  exact hp.trans ((congrArg (groupCohomology.H2π _) hd).trans (hq.symm.trans h))

include hval in
private theorem supportedDiagonal_infinite_coordinate_eq_zero
    (v : InfinitePlace K)
    (hi : infinitePlaceRestriction K v
      (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0) :
    groupCohomology.map (MonoidHom.id (Gal(E/K))) (supportedSPlaceInfiniteRepHom K E S v) 2
      (groupCohomology.H2π _ (supportedDiagonalCocycle E S z hval)) = 0 := by
  let c := dehomogenizeTwoOriginal (galoisUnitsRep K E) z
  let d := supportedDiagonalCocycle E S z hval
  let r := MonoidHom.id (Gal(E/K))
  have h := infinitePlaceTensorDiagonalH2_eq_zero_of_localization v E z hi
  let p := supportedSPlaceInfiniteRepHom K E S v
  let q := tensorDiagonalRepHom (K := K) (L := E) v.Completion
  have hd : groupCohomology.mapCocycles₂ r p d = groupCohomology.mapCocycles₂ r q c := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    change supportedSPlaceInfiniteRepHom K E S v
      (Additive.ofMul
        ⟨RelativeIdeleGroup.principalIdele K E (show Additive Eˣ from c (a, b)).toMul, _⟩) =
      tensorDiagonalRepHom v.Completion (c (a, b))
    rw [supportedSPlaceInfiniteRepHom_apply]
    exact infinitePlaceTensorDiagonal_principal v (show Additive Eˣ from c (a, b)).toMul
  have hp := groupCohomology.H2π_comp_map_apply r p d
  have hq := groupCohomology.H2π_comp_map_apply r q c
  exact hp.trans ((congrArg (groupCohomology.H2π _) hd).trans (hq.symm.trans h))

include hval in
private theorem supportedDiagonal_map_eq :
    groupCohomology.map (MonoidHom.id (Gal(E/K)))
        (GlobalClassFieldTheory.Cohomology.supportedIdeleInclusionRepHom K E S) 2
        (groupCohomology.H2π _ (supportedDiagonalCocycle E S z hval)) =
      groupCohomology.map (MonoidHom.id (Gal(E/K))) (finiteFieldUnitsIdeleRepHom K E) 2
        (groupCohomology.H2π _ (dehomogenizeTwoOriginal (galoisUnitsRep K E) z)) := by
  let r := MonoidHom.id (Gal(E/K))
  let p := GlobalClassFieldTheory.Cohomology.supportedIdeleInclusionRepHom K E S
  let q := finiteFieldUnitsIdeleRepHom K E
  let c := dehomogenizeTwoOriginal (galoisUnitsRep K E) z
  let d := supportedDiagonalCocycle E S z hval
  have hd : groupCohomology.mapCocycles₂ r p d = groupCohomology.mapCocycles₂ r q c := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    rfl
  have hp := groupCohomology.H2π_comp_map_apply r p d
  have hq := groupCohomology.H2π_comp_map_apply r q c
  exact hp.trans ((congrArg (groupCohomology.H2π _) hd).trans hq.symm)

include hval in
private theorem relativeClass_eq_zero_of_localizations
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
    (hf : ∀ v : HeightOneSpectrum (𝓞 K),
      finitePlaceRestriction K v (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0)
    (hi : ∀ v : InfinitePlace K,
      infinitePlaceRestriction K v (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0) :
    π (galoisUnitsRep K E) 2 z = 0 := by
  let A := Rep.ofMulDistribMulAction Gal(E/K) Supported
  let d := supportedDiagonalCocycle E S z hval
  let y := groupCohomology.H2π A d
  let r := MonoidHom.id (Gal(E/K))
  have hy : y = 0 :=
    supportedSPlaceH2_eq_zero_of_localizations K E S hfin y
      (fun v => supportedDiagonal_finite_coordinate_eq_zero E S z hval v (hf v.val))
      (fun v => supportedDiagonal_infinite_coordinate_eq_zero E S z hval v (hi v))
  apply (dehomogenizeTwoOriginal_class_eq_zero_iff (galoisUnitsRep K E) z).mp
  have hinj := finiteFieldUnitsIdeleH2Map_injective K E
  apply (injective_iff_map_eq_zero _).mp hinj
  let p := GlobalClassFieldTheory.Cohomology.supportedIdeleInclusionRepHom K E S
  let A' := (finiteIdeleShortComplex K E).X₂
  let f := groupCohomology.map (A := A) (B := A') r p 2
  exact (supportedDiagonal_map_eq E S z hval).symm.trans
    ((congrArg f hy).trans f.hom.map_zero)

private theorem placeRestriction_eq_zero_of_localization_eq_zero
    {k : Type*} [Field k] [NumberField k] (x : Br k) (hx : localization k x = 0)
    (v : Place k) : placeRestriction k v x = 0 := by
  have h := congrArg (fun a : ⨁ w : Place k, Br (placeCompletion k w) => a v) hx
  exact (localization_apply k x v).symm.trans (h.trans (DirectSum.zero_apply v))

/-- The actual localization map detects every global Brauer class. -/
private theorem localization_injective_native : Function.Injective (localization K) := by
  apply (injective_iff_map_eq_zero (localization K)).mpr
  intro x hx
  obtain ⟨E, z, he, hES⟩ := exists_finiteInflation_unit_support x
  let : NumberField E := NumberField.of_module_finite K E
  obtain ⟨S, hS⟩ := hES
  have hval (w : HeightOneSpectrum (𝓞 E)) (hw : finitePlaceBelow (K := K) w ∉ S) := (hS w hw).2
  have hfin (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      ChosenFinitePlaceIsUnramified (K := K) (L := E) v := by
    let w := chosenFinitePlaceExtension (L := E) v
    let W := finitePlaceExtensionCentre v w
    have hW : finitePlaceBelow (K := K) W ∉ S := by
      rw [finitePlaceBelow_finitePlaceExtensionCentre]
      exact hv
    exact chosenFinitePlaceIsUnramified_of_isUnramifiedAt v (hS W hW).1
  have hf (v : HeightOneSpectrum (𝓞 K)) :
      finitePlaceRestriction K v (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0 := by
    rw [he]
    exact placeRestriction_eq_zero_of_localization_eq_zero x hx (Sum.inl v)
  have hi (v : InfinitePlace K) :
      infinitePlaceRestriction K v (finiteInflation E (π (galoisUnitsRep K E) 2 z)) = 0 := by
    rw [he]
    exact placeRestriction_eq_zero_of_localization_eq_zero x hx (Sum.inr v)
  rw [← he, relativeClass_eq_zero_of_localizations E S z hval hfin hf hi, map_zero]

end ClassFieldTheory.Brauer

namespace ClassFieldTheory.Brauer

universe u v

private theorem restriction_square
    {A B : Type u} {C D : Type v} [Field A] [Field B] [Field C] [Field D]
    (f : A →+* B) (g : C →+* D) (e : A →+* C) (j : B →+* D) (h : j.comp f = g.comp e)
    (x : Br A) : restrict g (restrictAcross e x) = restrictAcross j (restrict f x) := by
  rw [← restrictAcross_same f, ← restrictAcross_same g, ← AddMonoidHom.comp_apply,
    restrictAcross_comp, ← h, ← restrictAcross_comp, AddMonoidHom.comp_apply]

private theorem restrictAcross_square_eq_zero
    {A B : Type u} {C D : Type v} [Field A] [Field B] [Field C] [Field D]
    (f : A →+* B) (g : C →+* D) (e : A →+* C) (j : B →+* D) (h : j.comp f = g.comp e)
    (x : Br A) (hx : restrict f x = 0) : restrict g (restrictAcross e x) = 0 := by
  let b := restrictAcross j
  exact (restriction_square f g e j h x).trans ((congrArg b hx).trans b.map_zero)

private theorem localization_zero_of_equiv
    {K : Type u} {S : Type v} [Field K] [NumberField K] [Field S] [NumberField S]
    (e : K ≃ₐ[ℚ] S) (x : Br K) (hx : localization K x = 0) :
    localization S (restrictAcross e.toRingHom x) = 0 := by
  apply DirectSum.ext
  intro w
  rw [localization_apply, DirectSum.zero_apply]
  cases w with
  | inl w =>
    let v := (finitePlaceCongr e).symm w
    let j := finitePlaceAdicCompletionCongrEquiv e w
    let : Algebra K S := e.toRingHom.toAlgebra
    have hv : finitePlaceBelow (K := K) w = v := finitePlaceBelow_eq_finitePlaceCongr_symm e w
    have h : j.toRingHom.comp (algebraMap K (v.adicCompletion K)) =
        (algebraMap S (w.adicCompletion S)).comp e.toRingHom := by
      apply RingHom.ext
      intro a
      change finitePlaceAdicCompletionMap K S v ⟨w, hv⟩ (a : v.adicCompletion K) = _
      rw [finitePlaceAdicCompletionMap_coe]
      rfl
    change restrict (algebraMap S (w.adicCompletion S)) (restrictAcross e.toRingHom x) = 0
    have hxv : finitePlaceRestriction K v x = 0 := by
      exact placeRestriction_eq_zero_of_localization_eq_zero x hx (Sum.inl v)
    exact restrictAcross_square_eq_zero (algebraMap K (v.adicCompletion K))
      (algebraMap S (w.adicCompletion S)) e.toRingHom j.toRingHom h x hxv
  | inr w =>
    let v := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv e.toRingEquiv).symm w
    let j := infinitePlaceCompletionCongrEquiv e w
    have h : j.toRingHom.comp (algebraMap K v.Completion) =
        (algebraMap S w.Completion).comp e.toRingHom :=
      RingHom.ext (infinitePlaceCompletionCongrHom_algebraMap e w)
    change restrict (algebraMap S w.Completion) (restrictAcross e.toRingHom x) = 0
    have hxv : infinitePlaceRestriction K v x = 0 := by
      exact placeRestriction_eq_zero_of_localization_eq_zero x hx (Sum.inr v)
    have hxv' : restrict (algebraMap K v.Completion) x = 0 := hxv
    exact restrictAcross_square_eq_zero (algebraMap K v.Completion)
      (algebraMap S w.Completion) e.toRingHom j.toRingHom h x hxv'

variable (K : Type u) [Field K] [NumberField K]

/-- Actual restriction to every original completion detects the original global
Brauer class. The sole small number-field model is used through naturality. -/
theorem localization_injective : Function.Injective (localization K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  let : Small.{0} K := ClassFieldTheory.numberField_small K
  let S := Shrink.{0} K
  let : NumberField S := ClassFieldTheory.numberField_shrink K
  let e : K ≃ₐ[ℚ] S := (Shrink.ringEquiv K).symm.toRatAlgEquiv
  let y := restrictAcross e.toRingHom x
  have hy : localization S y = 0 := localization_zero_of_equiv e x hx
  have hy₀ : y = 0 := (localization_injective_native (K := S))
    (hy.trans (map_zero (localization S)).symm)
  apply restrictAcross_injective_of_ringEquiv e.toRingEquiv
  exact hy₀.trans (map_zero (restrictAcross e.toRingHom)).symm

end ClassFieldTheory.Brauer
